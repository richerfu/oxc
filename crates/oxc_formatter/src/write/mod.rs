mod array_element_list;
mod array_expression;
mod array_pattern;
mod arrow_function_expression;
mod as_or_satisfies_expression;
mod assignment_pattern_property_list;
mod binary_like_expression;
mod binding_property_list;
mod block_statement;
mod call_arguments;
mod class;
mod decorators;
mod export_declarations;
mod function;
mod function_type;
mod import_declaration;
mod import_expression;
mod intersection_type;
mod jsx;
mod mapped_type;
mod member_expression;
mod object_like;
mod object_pattern_like;
mod parameters;
mod program;
mod return_or_throw_statement;
mod semicolon;
mod sequence_expression;
mod switch_statement;
mod template;
mod try_statement;
mod tuple_type;
mod type_parameters;
mod union_type;
mod variable_declaration;

pub use arrow_function_expression::{
    FormatJsArrowFunctionExpression, FormatJsArrowFunctionExpressionOptions,
};
pub use binary_like_expression::{BinaryLikeExpression, should_flatten};
pub use function::FormatFunctionOptions;

use cow_utils::CowUtils;

use oxc_allocator::{StringBuilder, Vec};
use oxc_ast::ast::*;
use oxc_span::GetSpan;

use crate::{
    ast_nodes::{AstNode, AstNodes},
    best_fitting, format_args,
    formatter::{
        Buffer, Format, Formatter,
        prelude::*,
        separated::FormatSeparatedIter,
        token::number::{NumberFormatOptions, format_number_token},
        trivia::{
            DanglingIndentMode, FormatDanglingComments, FormatLeadingComments,
            FormatTrailingComments,
        },
    },
    options::{FormatTrailingCommas, Semicolons, TrailingSeparator},
    parentheses::NeedsParentheses,
    utils::{
        array::write_array_node,
        assignment_like::AssignmentLike,
        call_expression::is_test_call_expression,
        conditional::ConditionalLike,
        expression::ExpressionLeftSide,
        format_node_without_trailing_comments::FormatNodeWithoutTrailingComments,
        member_chain::MemberChain,
        object::{format_property_key, should_preserve_quote},
        statement_body::FormatStatementBody,
        string::{FormatLiteralStringToken, StringLiteralParentKind},
    },
    write,
    write::parameters::can_avoid_parentheses,
};

use self::{
    array_expression::FormatArrayExpression,
    arrow_function_expression::is_multiline_template_starting_on_same_line,
    block_statement::is_empty_block,
    call_arguments::is_simple_module_import,
    class::format_grouped_parameters_with_return_type_for_method,
    object_like::ObjectLike,
    object_pattern_like::ObjectPatternLike,
    return_or_throw_statement::FormatAdjacentArgument,
    semicolon::OptionalSemicolon,
    type_parameters::{FormatTSTypeParameters, FormatTSTypeParametersOptions},
};

pub trait FormatWrite<'ast, T = ()> {
    fn write(&self, f: &mut Formatter<'_, 'ast>);
    fn write_with_options(&self, _options: T, _f: &mut Formatter<'_, 'ast>) {
        unreachable!("Please implement it first.");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, IdentifierName<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let text = text_without_whitespace(self.name().as_str());
        let is_property_key_parent = matches!(
            self.parent,
            AstNodes::ObjectProperty(_)
                | AstNodes::TSPropertySignature(_)
                | AstNodes::TSMethodSignature(_)
                | AstNodes::MethodDefinition(_)
                | AstNodes::PropertyDefinition(_)
                | AstNodes::AccessorProperty(_)
                | AstNodes::ImportAttribute(_)
        );
        if is_property_key_parent && f.context().is_quote_needed() {
            let quote_str = f.options().quote_style.as_str();
            write!(f, [quote_str, text, quote_str]);
        } else {
            write!(f, text);
        }
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, IdentifierReference<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, text_without_whitespace(self.name().as_str()));
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, BindingIdentifier<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, text_without_whitespace(self.name().as_str()));
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, LabelIdentifier<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, text_without_whitespace(self.name().as_str()));
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, ThisExpression> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, "this");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, ArrayExpression<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        FormatArrayExpression::new(self).fmt(f);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, Elision> {
    fn write(&self, _f: &mut Formatter<'_, 'a>) {}
}

impl<'a> FormatWrite<'a> for AstNode<'a, ObjectExpression<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        if f.options().quote_properties.is_consistent() {
            let quote_needed = self.properties.iter().any(|kind| {
                kind.as_property().is_some_and(|property| should_preserve_quote(&property.key, f))
            });
            f.context_mut().push_quote_needed(quote_needed);
        }

        ObjectLike::ObjectExpression(self).fmt(f);

        if f.options().quote_properties.is_consistent() {
            f.context_mut().pop_quote_needed();
        }
    }
}

impl<'a> Format<'a> for AstNode<'a, Vec<'a, ObjectPropertyKind<'a>>> {
    fn fmt(&self, f: &mut Formatter<'_, 'a>) {
        let trailing_separator = FormatTrailingCommas::ES5.trailing_separator(f.options());
        f.join_nodes_with_soft_line().entries_with_trailing_separator(
            self.iter(),
            ",",
            trailing_separator,
        );
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, ObjectProperty<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let is_accessor = match &self.kind() {
            PropertyKind::Init => false,
            PropertyKind::Get => {
                write!(f, ["get", space()]);
                true
            }
            PropertyKind::Set => {
                write!(f, ["set", space()]);
                true
            }
        };

        if self.method || is_accessor {
            let AstNodes::Function(value) = self.value().as_ast_nodes() else {
                unreachable!(
                    "The `value` always be a function node if `method` or `accessor` is true"
                )
            };

            if value.r#async() {
                write!(f, ["async", space()]);
            }
            if value.generator() {
                write!(f, "*");
            }
            if self.computed {
                write!(f, ["[", self.key(), "]"]);
            } else {
                format_property_key(self.key(), f);
            }

            format_grouped_parameters_with_return_type_for_method(
                value.type_parameters(),
                value.this_param.as_deref(),
                value.params(),
                value.return_type(),
                f,
            );

            if let Some(body) = &value.body() {
                write!(f, [space(), body]);
            }
        } else {
            // Check if this is an ArkUI leading-dot expression property
            // (value is LeadingDotExpression or CallExpression/StaticMemberExpression chain starting with LeadingDotExpression)
            let value = self.value();
            let is_leading_dot_expression = is_arkui_leading_dot_expression(value);

            if is_leading_dot_expression {
                // For ArkUI leading-dot expressions, skip key and ":", just format the value
                write!(f, value);
            } else {
                // Use normal object property formatting
                write!(f, AssignmentLike::ObjectProperty(self));
            }
        }
    }
}

/// Check if an expression is an ArkUI leading-dot expression (recursively)
/// This handles chained calls like .method1().method2()
fn is_arkui_leading_dot_expression<'a>(expr: &AstNode<'a, Expression<'a>>) -> bool {
    match expr.as_ast_nodes() {
        AstNodes::LeadingDotExpression(_) => true,
        AstNodes::CallExpression(call) => {
            // Check if the callee is a leading-dot expression or a chain starting with one
            is_arkui_leading_dot_expression(&call.callee())
        }
        AstNodes::StaticMemberExpression(member) => {
            // Check if the object is a leading-dot expression or a chain starting with one
            let object = member.object();
            match object.as_ast_nodes() {
                AstNodes::LeadingDotExpression(_) => true,
                _ => {
                    // Recursively check the object
                    is_arkui_leading_dot_expression(object)
                }
            }
        }
        _ => false,
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, LeadingDotExpression<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let optional = self.optional();
        let expression = self.expression();

        // Format: .expression or ?.expression
        // The expression field contains the full chain (e.g., fontSize(size).fancy(12).hello())
        write!(
            f,
            [group(&format_args!(
                soft_line_break_or_space(),
                optional.then_some("?.").unwrap_or("."),
                expression
            ))]
        );
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, CallExpression<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let callee = self.callee();
        let type_arguments = self.type_arguments();
        let arguments = self.arguments();
        let optional = self.optional();

        let is_template_literal_single_arg = arguments.len() == 1
            && arguments.first().unwrap().as_expression().is_some_and(|expr| {
                is_multiline_template_starting_on_same_line(expr, f.source_text())
            });

        if !is_template_literal_single_arg
            && matches!(
                callee.as_ref(),
                Expression::StaticMemberExpression(_) | Expression::ComputedMemberExpression(_)
            )
            && !is_simple_module_import(self.arguments(), f.comments())
            && !is_test_call_expression(self)
        {
            MemberChain::from_call_expression(self, f).fmt(f);
        } else {
            let format_inner = format_with(|f| {
                // Preserve trailing comments of the callee in the following cases:
                // `call /**/()`
                // `call /**/<T>()`
                if self.type_arguments.is_some() {
                    write!(f, [callee]);
                } else {
                    write!(f, [FormatNodeWithoutTrailingComments(callee)]);

                    if self.arguments.is_empty() {
                        let callee_trailing_comments = f
                            .context()
                            .comments()
                            .comments_before_character(self.callee.span().end, b'(');
                        write!(f, FormatTrailingComments::Comments(callee_trailing_comments));
                    }
                }
                write!(f, [optional.then_some("?."), type_arguments, arguments]);
            });
            if matches!(callee.as_ref(), Expression::CallExpression(_)) {
                write!(f, [group(&format_inner)]);
            } else {
                write!(f, [format_inner]);
            }
        }
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, NewExpression<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, ["new", space(), self.callee(), self.type_arguments(), self.arguments()]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, MetaProperty<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, [self.meta(), ".", self.property()]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, SpreadElement<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, ["...", self.argument()]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, UpdateExpression<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        if self.prefix() {
            write!(f, self.operator().as_str());
        }
        write!(f, self.argument());
        if !self.prefix() {
            write!(f, self.operator().as_str());
        }
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, UnaryExpression<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, self.operator().as_str());
        if self.operator().is_keyword() {
            write!(f, space());
        }
        let Span { start, end, .. } = self.argument.span();
        if f.comments().has_comment_before(start)
            || f.comments().has_comment_in_range(end, self.span().end)
        {
            write!(
                f,
                [group(&format_args!(token("("), soft_block_indent(self.argument()), token(")")))]
            );
        } else {
            write!(f, self.argument());
        }
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, BinaryExpression<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        BinaryLikeExpression::BinaryExpression(self).fmt(f);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, PrivateInExpression<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, [self.left(), space(), "in", space(), self.right()]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, LogicalExpression<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        BinaryLikeExpression::LogicalExpression(self).fmt(f);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, ConditionalExpression<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        ConditionalLike::ConditionalExpression(self).fmt(f);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, AssignmentExpression<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        AssignmentLike::AssignmentExpression(self).fmt(f);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, ArrayAssignmentTarget<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, "[");

        if self.elements.is_empty() && self.rest.is_none() {
            write!(f, [format_dangling_comments(self.span()).with_block_indent()]);
        } else {
            write!(
                f,
                group(&soft_block_indent(&format_with(|f| {
                    let has_element = !self.elements.is_empty();
                    if has_element {
                        write_array_node(
                            self.elements.len() + usize::from(self.rest.is_some()),
                            self.elements().iter().map(AstNode::as_ref),
                            f,
                        );
                    }
                    if let Some(rest) = self.rest() {
                        write!(f, [has_element.then_some(soft_line_break_or_space()), rest]);
                    }
                })))
            );
        }

        write!(f, "]");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, ObjectAssignmentTarget<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        ObjectPatternLike::ObjectAssignmentTarget(self).fmt(f);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, AssignmentTargetRest<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, ["...", self.target()]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, AssignmentTargetWithDefault<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, [self.binding(), space(), "=", space(), self.init()]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, AssignmentTargetPropertyIdentifier<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, self.binding());
        if let Some(expr) = &self.init() {
            write!(f, [space(), "=", space(), expr]);
        }
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, AssignmentTargetPropertyProperty<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        if self.computed() {
            write!(f, "[");
        }
        write!(f, self.name());
        if self.computed() {
            write!(f, "]");
        }
        write!(f, [":", space(), self.binding()]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, Super> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, "super");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, AwaitExpression<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let format_inner = format_with(|f| write!(f, ["await", space(), self.argument()]));

        let is_callee_or_object = match self.parent {
            AstNodes::StaticMemberExpression(_) => true,
            AstNodes::ComputedMemberExpression(member) => member.object.span() == self.span(),
            _ => self.parent.is_call_like_callee_span(self.span),
        };

        if is_callee_or_object {
            let mut await_expression = None;
            for ancestor in self.ancestors().skip(1) {
                match ancestor {
                    AstNodes::BlockStatement(_)
                    | AstNodes::FunctionBody(_)
                    | AstNodes::SwitchCase(_)
                    | AstNodes::Program(_)
                    | AstNodes::TSModuleBlock(_) => break,
                    AstNodes::AwaitExpression(expr) => await_expression = Some(expr),
                    _ => {}
                }
            }

            let indented = format_with(|f| write!(f, [soft_block_indent(&format_inner)]));

            return if let Some(expr) = await_expression.take() {
                if !expr.needs_parentheses(f)
                    && ExpressionLeftSide::leftmost(expr.argument()).span() != self.span()
                {
                    return write!(f, [group(&indented)]);
                }

                write!(f, [indented]);
            } else {
                write!(f, [group(&indented)]);
            };
        }

        write!(f, [format_inner]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, ChainExpression<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        self.expression().fmt(f);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, ParenthesizedExpression<'a>> {
    fn write(&self, _f: &mut Formatter<'_, 'a>) {
        unreachable!("No `ParenthesizedExpression` as we disabled `preserve_parens` in the parser")
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, EmptyStatement> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        if matches!(
            self.parent,
            AstNodes::DoWhileStatement(_)
                | AstNodes::IfStatement(_)
                | AstNodes::WhileStatement(_)
                | AstNodes::ForStatement(_)
                | AstNodes::ForInStatement(_)
                | AstNodes::ForOfStatement(_)
                | AstNodes::WithStatement(_)
        ) {
            write!(f, ";");
        }
    }
}

/// Returns `true` if the expression needs a leading semicolon to prevent ASI issues
fn expression_statement_needs_semicolon<'a>(
    stmt: &AstNode<'a, ExpressionStatement<'a>>,
    f: &Formatter<'_, 'a>,
) -> bool {
    if matches!(
        stmt.parent,
        // `if (true) (() => {})`
        AstNodes::IfStatement(_)
        // `do ({} => {}) while (true)`
        | AstNodes::DoWhileStatement(_)
        // `while (true) (() => {})`
        | AstNodes::WhileStatement(_)
        // `for (;;) (() => {})`
        | AstNodes::ForStatement(_)
        // `for (i in o) (() => {})`
        | AstNodes::ForInStatement(_)
        // `for (i of o) (() => {})`
        | AstNodes::ForOfStatement(_)
        // `with(true) (() => {})`
        | AstNodes::WithStatement(_)
        // `label: (() => {})`
        | AstNodes::LabeledStatement(_)
    ) {
        return false;
    }
    // Arrow functions need semicolon only if they will have parentheses
    // e.g., `(a) => {}` needs `;(a) => {}` but `a => {}` doesn't need semicolon
    if let Expression::ArrowFunctionExpression(arrow) = &stmt.expression {
        return !can_avoid_parentheses(arrow, f);
    }

    // First check if the expression itself needs protection
    let expr = stmt.expression();

    // Get the leftmost expression to check what the line starts with
    ExpressionLeftSide::from(expr).iter().any(|current| match current {
        ExpressionLeftSide::Expression(expr) => {
            expr.needs_parentheses(f)
                || match expr.as_ref() {
                    Expression::ArrayExpression(_)
                    | Expression::RegExpLiteral(_)
                    | Expression::TSTypeAssertion(_)
                    | Expression::ArrowFunctionExpression(_)
                    | Expression::JSXElement(_)
                    | Expression::TemplateLiteral(_) => true,
                    Expression::UnaryExpression(unary) => {
                        matches!(
                            unary.operator,
                            UnaryOperator::UnaryPlus | UnaryOperator::UnaryNegation
                        )
                    }
                    _ => false,
                }
        }
        ExpressionLeftSide::AssignmentTarget(assignment) => {
            matches!(
                assignment.as_ref(),
                AssignmentTarget::ArrayAssignmentTarget(_)
                    | AssignmentTarget::TSTypeAssertion(_)
                    | AssignmentTarget::TSAsExpression(_)
                    | AssignmentTarget::TSSatisfiesExpression(_)
            )
        }
        ExpressionLeftSide::SimpleAssignmentTarget(assignment) => {
            matches!(
                assignment.as_ref(),
                SimpleAssignmentTarget::TSTypeAssertion(_)
                    | SimpleAssignmentTarget::TSAsExpression(_)
                    | SimpleAssignmentTarget::TSSatisfiesExpression(_)
            )
        }
    })
}

impl<'a> FormatWrite<'a> for AstNode<'a, ExpressionStatement<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        // Check if we need a leading semicolon to prevent ASI issues
        if f.options().semicolons == Semicolons::AsNeeded
            && expression_statement_needs_semicolon(self, f)
        {
            write!(f, ";");
        }

        write!(f, [self.expression(), OptionalSemicolon]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, DoWhileStatement<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let body = self.body();
        write!(f, group(&format_args!("do", FormatStatementBody::new(body))));
        if matches!(body.as_ref(), Statement::BlockStatement(_)) {
            write!(f, space());
        } else {
            write!(f, hard_line_break());
        }
        write!(
            f,
            [
                "while",
                space(),
                "(",
                group(&soft_block_indent(&self.test())),
                ")",
                OptionalSemicolon
            ]
        );
    }
}

/// Formats comments that appear before empty statements in control structures.
///
/// Example:
/// ```js
/// // Input:
/// for (init;;) /* comment */ ;
/// for (init;;update) /* comment */ ;
/// for (init of iterable) /* comment */ ;
/// for (init in iterable) /* comment */ ;
/// while (test) /* comment */ ;
/// if (test) /* comment */ ;
///
/// // Output:
/// for (init /* comment */;; );
/// for (init; ; update /* comment */);
/// for (init of iterable /* comment */) ;
/// for (init in iterable /* comment */) ;
/// while (test /* comment */) ;
/// if (test /* comment */) ;
/// ```
///
/// This ensures compatibility with [Prettier's comment handling for empty statements](https://github.com/prettier/prettier/blob/7584432401a47a26943dd7a9ca9a8e032ead7285/src/language-js/comments/printer-methods.js#L15).
struct FormatCommentForEmptyStatement<'a, 'b>(&'b AstNode<'a, Statement<'a>>);
impl<'a> Format<'a> for FormatCommentForEmptyStatement<'a, '_> {
    fn fmt(&self, f: &mut Formatter<'_, 'a>) {
        if let AstNodes::EmptyStatement(empty) = self.0.as_ast_nodes() {
            let comments = f.context().comments().comments_before(empty.span.start);
            FormatTrailingComments::Comments(comments).fmt(f);
            empty.format_trailing_comments(f);
        }
    }
}

struct FormatTestOfIfAndWhileStatement<'a, 'b>(&'b AstNode<'a, Expression<'a>>);
impl<'a> Format<'a> for FormatTestOfIfAndWhileStatement<'a, '_> {
    fn fmt(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, FormatNodeWithoutTrailingComments(self.0));
        let comments = f.context().comments().comments_before_character(self.0.span().end, b')');
        if !comments.is_empty() {
            write!(f, [space(), FormatTrailingComments::Comments(comments)]);
        }
    }
}
impl<'a> FormatWrite<'a> for AstNode<'a, WhileStatement<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let body = self.body();
        write!(
            f,
            group(&format_args!(
                "while",
                space(),
                "(",
                group(&soft_block_indent(&format_args!(
                    FormatTestOfIfAndWhileStatement(self.test()),
                    FormatCommentForEmptyStatement(self.body())
                ))),
                ")",
                FormatStatementBody::new(body)
            ))
        );
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, ForStatement<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let init = self.init();
        let test = self.test();
        let update = self.update();
        let body = self.body();
        let format_body = FormatStatementBody::new(body);
        if init.is_none() && test.is_none() && update.is_none() {
            let comments = f.context().comments().comments_before(body.span().start);
            if !comments.is_empty() {
                write!(
                    f,
                    [
                        FormatDanglingComments::Comments {
                            comments,
                            indent: DanglingIndentMode::None
                        },
                        soft_line_break_or_space()
                    ]
                );
            }
            return write!(f, [group(&format_args!("for", space(), "(;;)", format_body))]);
        }

        let format_inner = format_with(|f| {
            write!(
                f,
                [
                    "for",
                    space(),
                    "(",
                    group(&soft_block_indent(&format_args!(
                        init,
                        (test.is_none() && update.is_none())
                            .then_some(FormatCommentForEmptyStatement(body)),
                        ";",
                        soft_line_break_or_space(),
                        test,
                        (update.is_none()).then_some(FormatCommentForEmptyStatement(body)),
                        ";",
                        soft_line_break_or_space(),
                        update,
                        FormatCommentForEmptyStatement(body)
                    ))),
                    ")",
                    format_body
                ]
            );
        });
        write!(f, group(&format_inner));
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, ForInStatement<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let comments = f.context().comments().own_line_comments_before(self.right.span().start);
        let body = self.body();
        write!(
            f,
            [
                FormatLeadingComments::Comments(comments),
                group(&format_args!(
                    "for",
                    space(),
                    "(",
                    self.left(),
                    space(),
                    "in",
                    space(),
                    self.right(),
                    FormatCommentForEmptyStatement(body),
                    ")",
                    FormatStatementBody::new(body)
                ))
            ]
        );
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, ForOfStatement<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let comments = f.context().comments().own_line_comments_before(self.right.span().start);

        let r#await = self.r#await();
        let left = self.left();
        let right = self.right();
        let body = self.body();
        let format_inner = format_with(|f| {
            write!(f, "for");
            if r#await {
                write!(f, [space(), "await"]);
            }
            write!(
                f,
                [
                    space(),
                    "(",
                    left,
                    space(),
                    "of",
                    space(),
                    right,
                    FormatCommentForEmptyStatement(body),
                    ")",
                    FormatStatementBody::new(body)
                ]
            );
        });
        write!(f, [FormatLeadingComments::Comments(comments), group(&format_inner)]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, IfStatement<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let test = self.test();
        let consequent = self.consequent();
        let alternate = self.alternate();

        write!(
            f,
            group(&format_args!(
                "if",
                space(),
                "(",
                group(&soft_block_indent(&FormatTestOfIfAndWhileStatement(test))),
                ")",
                FormatStatementBody::new(consequent),
            ))
        );
        if let Some(alternate) = alternate {
            let alternate_start = alternate.span().start;
            let comments = f.context().comments().comments_before(alternate_start);

            let has_line_comment = comments.iter().any(|comment| comment.is_line());
            let has_dangling_comments = comments
                .last()
                .or(f.comments().printed_comments().last())
                .is_some_and(|last_comment| {
                    // Ensure the comments are placed before the else keyword or on a new line
                    f.source_text().slice_range(last_comment.span.end, alternate_start).trim()
                        == "else"
                });

            let else_on_same_line = matches!(consequent.as_ref(), Statement::BlockStatement(_))
                && (!has_line_comment || !has_dangling_comments);

            if else_on_same_line {
                write!(f, [space(), has_dangling_comments.then(line_suffix_boundary)]);
            } else {
                write!(f, hard_line_break());
            }

            if has_dangling_comments && let Some(first_comment) = comments.first() {
                if f.source_text().get_lines_before(first_comment.span, f.comments()) > 1 {
                    write!(f, empty_line());
                }
                write!(
                    f,
                    FormatDanglingComments::Comments { comments, indent: DanglingIndentMode::None }
                );
                if has_line_comment {
                    write!(f, hard_line_break());
                } else {
                    write!(f, space());
                }
            }

            write!(
                f,
                [
                    "else",
                    line_suffix_boundary(),
                    group(&FormatStatementBody::new(alternate).with_forced_space(matches!(
                        alternate.as_ref(),
                        Statement::IfStatement(_)
                    )))
                ]
            );
        }
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, ContinueStatement<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, "continue");
        if let Some(label) = self.label() {
            write!(f, [space(), label]);
        }
        write!(f, OptionalSemicolon);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, BreakStatement<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, "break");
        if let Some(label) = self.label() {
            write!(f, [space(), label]);
        }
        write!(f, OptionalSemicolon);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, WithStatement<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(
            f,
            group(&format_args!(
                "with",
                space(),
                "(",
                self.object(),
                ")",
                FormatStatementBody::new(self.body())
            ))
        );
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, LabeledStatement<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let comments = f.context().comments().line_comments_before(self.body.span().start);
        FormatLeadingComments::Comments(comments).fmt(f);

        let label = self.label();
        let body = self.body();
        write!(f, [label, ":"]);
        if matches!(body.as_ref(), Statement::EmptyStatement(_)) {
            let empty_comments = f.context().comments().comments_before(self.span.end);
            write!(
                f,
                [
                    FormatTrailingComments::Comments(empty_comments),
                    maybe_space(!empty_comments.is_empty()),
                    // If the body is an empty statement, force semicolon insertion
                    ";"
                ]
            );
        } else {
            write!(f, [space(), body]);
        }
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, DebuggerStatement> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, ["debugger", OptionalSemicolon]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, BindingPattern<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        Format::fmt(self, f);
        if let AstNodes::VariableDeclarator(declarator) = self.parent {
            write!(f, declarator.definite.then_some("!"));
        }
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, FormalParameterRest<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, [self.rest()]);
        write!(f, self.type_annotation());
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, AssignmentPattern<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let left = self.left().memoized();
        // Format `left` early before writing leading comments, so that comments
        // inside `left` are not treated as leading comments of `= right`
        left.inspect(f);
        let comments = f.context().comments().own_line_comments_before(self.right.span().start);
        write!(
            f,
            [
                FormatLeadingComments::Comments(comments),
                group(&left),
                space(),
                "=",
                space(),
                self.right()
            ]
        );
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, ObjectPattern<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        ObjectPatternLike::ObjectPattern(self).fmt(f);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, BindingProperty<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        AssignmentLike::BindingProperty(self).fmt(f);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, BindingRestElement<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, ["...", self.argument()]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, YieldExpression<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, ["yield", self.delegate().then_some("*")]);
        if let Some(argument) = &self.argument() {
            write!(f, [space(), FormatAdjacentArgument(argument)]);
        }
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, V8IntrinsicExpression<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, ["%", self.name(), self.arguments()]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, BooleanLiteral> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, if self.value() { "true" } else { "false" });
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, NullLiteral> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, "null");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, NumericLiteral<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        format_number_token(
            f.source_text().text_for(self),
            NumberFormatOptions::keep_one_trailing_decimal_zero(),
        )
        .fmt(f);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, StringLiteral<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let is_jsx = matches!(self.parent, AstNodes::JSXAttribute(_));
        FormatLiteralStringToken::new(
            f.source_text().text_for(self),
            /* jsx */
            is_jsx,
            StringLiteralParentKind::Expression,
        )
        .fmt(f);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, BigIntLiteral<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(
            f,
            text(f.context().allocator().alloc_str(&self.raw().unwrap().cow_to_ascii_lowercase()))
        );
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, RegExpLiteral<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let raw = self.raw().unwrap().as_str();
        let (pattern, flags) = raw.rsplit_once('/').unwrap();
        // TODO: print the flags without allocation.
        let mut flags = flags.chars().collect::<std::vec::Vec<_>>();
        flags.sort_unstable();
        let flags = flags.iter().collect::<String>();
        let s = StringBuilder::from_strs_array_in([pattern, "/", &flags], f.context().allocator());
        write!(f, text(s.into_str()));
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSEnumDeclaration<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        if self.declare() {
            write!(f, ["declare", space()]);
        }
        if self.r#const() {
            write!(f, ["const", space()]);
        }
        write!(f, ["enum", space(), self.id(), space(), "{", self.body(), "}"]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSEnumBody<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        if self.members().is_empty() {
            write!(
                f,
                group(&format_args!(format_dangling_comments(self.span()), soft_line_break()))
            );
        } else {
            write!(f, block_indent(self.members()));
        }
    }
}

impl<'a> Format<'a> for AstNode<'a, Vec<'a, TSEnumMember<'a>>> {
    fn fmt(&self, f: &mut Formatter<'_, 'a>) {
        let trailing_separator = FormatTrailingCommas::ES5.trailing_separator(f.options());
        f.join_nodes_with_soft_line().entries_with_trailing_separator(
            self.iter(),
            ",",
            trailing_separator,
        );
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSEnumMember<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let id = self.id();
        let is_computed = matches!(id.as_ref(), TSEnumMemberName::ComputedTemplateString(_));

        if is_computed {
            write!(f, "[");
        }

        write!(f, [id]);

        if is_computed {
            write!(f, "]");
        }

        if let Some(init) = self.initializer() {
            write!(f, [space(), "=", space(), init]);
        }
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSTypeAnnotation<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        match self.parent {
            AstNodes::TSFunctionType(_) | AstNodes::TSConstructorType(_) => {
                write!(f, ["=>", space(), self.type_annotation()]);
            }
            AstNodes::TSTypePredicate(_) => {
                write!(f, [self.type_annotation()]);
            }
            _ => {
                write!(f, [":", space(), self.type_annotation()]);
            }
        }
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSLiteralType<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        self.literal().fmt(f);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSConditionalType<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        ConditionalLike::TSConditionalType(self).fmt(f);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSParenthesizedType<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, ["(", self.type_annotation(), ")"]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSTypeOperator<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let needs_parentheses = self.needs_parentheses(f);
        if needs_parentheses {
            write!(f, "(");
        }

        write!(f, [self.operator().to_str(), hard_space(), self.type_annotation()]);

        if needs_parentheses {
            write!(f, ")");
        }
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSArrayType<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, [self.element_type(), "[]"]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSIndexedAccessType<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, [self.object_type(), "[", self.index_type(), "]"]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSNamedTupleMember<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, self.label());
        if self.optional() {
            write!(f, "?");
        }
        write!(f, [":", space(), self.element_type()]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSOptionalType<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, [self.type_annotation(), "?"]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSRestType<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, ["...", self.type_annotation()]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSAnyKeyword> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, "any");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSStringKeyword> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, "string");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSBooleanKeyword> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, "boolean");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSNumberKeyword> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, "number");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSNeverKeyword> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, "never");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSIntrinsicKeyword> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, "intrinsic");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSUnknownKeyword> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, "unknown");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSNullKeyword> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, "null");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSUndefinedKeyword> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, "undefined");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSVoidKeyword> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, "void");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSSymbolKeyword> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, "symbol");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSThisType> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, "this");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSObjectKeyword> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, "object");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSBigIntKeyword> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, "bigint");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSTypeReference<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, [self.type_name(), self.type_arguments()]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSQualifiedName<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, [self.left(), ".", self.right()]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSTypeParameterDeclaration<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        FormatTSTypeParameters::new(self, FormatTSTypeParametersOptions::default()).fmt(f);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSTypeAliasDeclaration<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, [AssignmentLike::TSTypeAliasDeclaration(self), OptionalSemicolon]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSInterfaceDeclaration<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let id = self.id();
        let type_parameters = self.type_parameters();
        let extends = self.extends();
        let body = self.body();

        // Determines whether to use group mode for formatting the `extends` clause.
        // 1. If there are multiple `extends`, we always use group mode.
        // 2. If there is a single `extends` that is a member expression without type arguments, we use group mode.
        // 3. If there are comments between the `id` and the `extends`, we use group mode.
        let group_mode = extends.len() > 1
            || extends.as_ref().first().is_some_and(|first| {
                (first.expression.is_member_expression() && first.type_arguments.is_none()) || {
                    let prev_span = type_parameters.as_ref().map_or(id.span(), GetSpan::span);
                    f.comments().has_comment_in_range(prev_span.end, first.span().start)
                }
            });

        let format_id = format_with(|f| {
            if type_parameters.is_none() && extends.is_empty() {
                FormatNodeWithoutTrailingComments(id).fmt(f);
            } else {
                write!(f, [id]);
            }

            if let Some(type_parameters) = type_parameters {
                let type_parameters_group = Some(f.group_id("type_parameters"));
                write!(
                    f,
                    FormatTSTypeParameters::new(
                        type_parameters,
                        FormatTSTypeParametersOptions {
                            group_id: type_parameters_group,
                            is_type_or_interface_decl: true
                        }
                    )
                );
            }
        });

        let format_extends = format_with(|f| {
            let Some(first_extend) = extends.as_ref().first() else {
                return;
            };

            let has_leading_own_line_comment =
                f.context().comments().has_leading_own_line_comment(first_extend.span().start);

            if has_leading_own_line_comment {
                write!(
                    f,
                    FormatTrailingComments::Comments(
                        f.context().comments().comments_before(first_extend.span().start)
                    )
                );
            }

            if extends.len() > 1 {
                write!(
                    f,
                    [
                        soft_line_break_or_space(),
                        "extends",
                        group(&soft_line_indent_or_space(extends))
                    ]
                );
            } else {
                let format_extends =
                    format_with(|f| write!(f, [space(), "extends", space(), extends]));
                if group_mode {
                    write!(f, [soft_line_break_or_space(), group(&format_extends)]);
                } else {
                    write!(f, format_extends);
                }
            }

            let has_leading_own_line_comment =
                f.context().comments().has_leading_own_line_comment(self.body.span().start);

            if !has_leading_own_line_comment {
                write!(f, [space()]);
                body.format_leading_comments(f);
            }
        });

        let content = format_with(|f| {
            if self.declare() {
                write!(f, ["declare", space()]);
            }

            write!(f, ["interface", space()]);

            if extends.is_empty() {
                write!(f, [format_id, format_extends]);
            } else if group_mode {
                let indented = format_with(|f| write!(f, [format_id, indent(&format_extends)]));
                let heritage_id = f.group_id("heritageGroup");
                write!(f, [group(&indented).with_group_id(Some(heritage_id)), space()]);
            } else {
                write!(f, [&format_args!(format_id, format_extends)]);
            }

            write!(f, [space()]);
            // Avoid printing leading comments of body
            body.write(f);
        });

        write!(f, group(&content));
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSInterfaceBody<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, [space(), "{"]);

        if self.body.is_empty() {
            write!(f, format_dangling_comments(self.span).with_block_indent());
        } else {
            write!(f, block_indent(&self.body()));
        }

        write!(f, "}");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSPropertySignature<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        if self.readonly() {
            write!(f, ["readonly", space()]);
        }
        if self.computed() {
            write!(f, ["[", self.key(), "]"]);
        } else {
            format_property_key(self.key(), f);
        }
        if self.optional() {
            write!(f, "?");
        }
        if let Some(type_annotation) = &self.type_annotation() {
            write!(f, type_annotation);
        }
    }
}

struct FormatTSSignature<'a, 'b> {
    signature: &'b AstNode<'a, TSSignature<'a>>,
    next_signature: Option<&'b AstNode<'a, TSSignature<'a>>>,
}

impl GetSpan for FormatTSSignature<'_, '_> {
    fn span(&self) -> Span {
        self.signature.span()
    }
}

impl<'a> Format<'a> for FormatTSSignature<'a, '_> {
    fn fmt(&self, f: &mut Formatter<'_, 'a>) {
        if f.comments().is_suppressed(self.signature.span().start) {
            return write!(f, [self.signature]);
        }

        write!(f, [&self.signature]);

        match f.options().semicolons {
            Semicolons::Always => {
                if self.next_signature.is_none() {
                    write!(f, [if_group_breaks(&token(";"))]);
                } else {
                    token(";").fmt(f);
                }
            }
            Semicolons::AsNeeded => {
                // Needs semicolon anyway when:
                // 1. It's a non-computed property signature with type annotation followed by
                //    a call signature that has type parameters
                //    e.g for: `a: string; <T>() => void`
                // 2. It's a non-computed property signature without type annotation followed by
                //    a call signature or method signature
                //    e.g for: `a; () => void` or `a; method(): void`
                let needs_semicolon = matches!(
                    self.signature.as_ref(), TSSignature::TSPropertySignature(property) if !property.computed
                    && self.next_signature.is_some_and(|signature| match signature.as_ref() {
                        TSSignature::TSCallSignatureDeclaration(call) => {
                            property.type_annotation.is_none() || call.type_parameters.is_some()
                        }
                        TSSignature::TSMethodSignature(_) => property.type_annotation.is_none(),
                        _ => false,
                    })
                );

                if needs_semicolon {
                    write!(f, [";"]);
                } else if self.next_signature.is_some() {
                    write!(f, [if_group_fits_on_line(&token(";"))]);
                }
            }
        }
    }
}

impl<'a> Format<'a> for AstNode<'a, Vec<'a, TSSignature<'a>>> {
    fn fmt(&self, f: &mut Formatter<'_, 'a>) {
        if f.options().quote_properties.is_consistent() {
            let quote_needed = self.as_ref().iter().any(|signature| {
                let key = match signature {
                    TSSignature::TSPropertySignature(property) => &property.key,
                    TSSignature::TSMethodSignature(property) => &property.key,
                    _ => return false,
                };
                should_preserve_quote(key, f)
            });
            f.context_mut().push_quote_needed(quote_needed);
        }

        let mut joiner = f.join_nodes_with_soft_line();

        let mut iter = self.iter().peekable();
        while let Some(signature) = iter.next() {
            joiner.entry(
                signature.span(),
                &FormatTSSignature { signature, next_signature: iter.peek().copied() },
            );
        }

        if f.options().quote_properties.is_consistent() {
            f.context_mut().pop_quote_needed();
        }
    }
}

impl<'a> Format<'a> for AstNode<'a, Vec<'a, TSInterfaceHeritage<'a>>> {
    fn fmt(&self, f: &mut Formatter<'_, 'a>) {
        let last_index = self.len().saturating_sub(1);
        let mut joiner = f.join_with(soft_line_break_or_space());

        for (i, heritage) in FormatSeparatedIter::new(self.into_iter(), ",")
            .with_trailing_separator(TrailingSeparator::Disallowed)
            .enumerate()
        {
            if i == last_index {
                // The trailing comments of the last heritage should be printed inside the interface declaration
                joiner.entry(&FormatNodeWithoutTrailingComments(&heritage));
            } else {
                joiner.entry(&heritage);
            }
        }
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSInterfaceHeritage<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, [self.expression(), self.type_arguments()]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSTypePredicate<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        if self.asserts() {
            write!(f, ["asserts", space()]);
        }
        write!(f, [self.parameter_name()]);
        if let Some(type_annotation) = self.type_annotation() {
            write!(f, [space(), "is", space(), type_annotation]);
        }
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSModuleDeclaration<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        if self.declare() {
            write!(f, ["declare", space()]);
        }

        write!(f, self.kind().as_str());

        write!(f, [space(), self.id()]);

        if let Some(body) = self.body() {
            let mut body = body;
            loop {
                match body.as_ast_nodes() {
                    AstNodes::TSModuleDeclaration(b) => {
                        write!(f, [".", b.id()]);
                        if let Some(b) = &b.body() {
                            body = b;
                        } else {
                            break;
                        }
                    }
                    AstNodes::TSModuleBlock(body) => {
                        write!(f, [space(), body]);
                        break;
                    }
                    _ => {
                        unreachable!()
                    }
                }
            }
        } else {
            write!(f, OptionalSemicolon);
        }
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSGlobalDeclaration<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        if self.declare {
            write!(f, ["declare", space()]);
        }
        let comments_before_global = f.context().comments().comments_before(self.global_span.start);
        write!(f, FormatLeadingComments::Comments(comments_before_global));
        write!(f, ["global", space(), self.body()]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSModuleBlock<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let directives = self.directives();
        let body = self.body();
        let span = self.span();

        write!(f, "{");
        if is_empty_block(&self.body) && directives.is_empty() {
            write!(f, [format_dangling_comments(span).with_block_indent()]);
        } else {
            write!(f, [block_indent(&format_args!(directives, body))]);
        }
        write!(f, "}");
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSTypeLiteral<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        ObjectLike::TSTypeLiteral(self).fmt(f);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSInferType<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, ["infer ", self.type_parameter()]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSTypeQuery<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, ["typeof ", self.expr_name(), self.type_arguments()]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSImportType<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, ["import("]);

        let has_comment = f.context().comments().has_comment_before(self.source.span().start);

        let format_argument = self.source().memoized();
        let format_options = self.options().memoized();

        if has_comment || self.options().is_some() {
            let format_inner = format_with(|f| {
                write!(
                    f,
                    [
                        format_argument,
                        &format_with(|f| {
                            if self.options.is_some() {
                                write!(f, [",", soft_line_break_or_space(), format_options]);
                            }
                        }),
                    ]
                );
            });
            if has_comment {
                write!(f, [&soft_block_indent(&format_inner)]);
            } else if self.options().is_some() {
                write!(f, [best_fitting!(format_inner, &soft_block_indent(&format_inner))]);
            } else {
                write!(f, [format_inner]);
            }
        } else {
            write!(f, self.source());
        }

        write!(f, ")");
        if let Some(qualified_name) = &self.qualifier() {
            write!(f, [".", qualified_name]);
        }
        write!(f, self.type_arguments());
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSImportTypeQualifiedName<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, [self.left(), ".", self.right()]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSTypeAssertion<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let break_after_cast = !matches!(
            self.expression,
            Expression::ArrayExpression(_) | Expression::ObjectExpression(_)
        );

        let format_cast = format_with(|f| {
            write!(f, ["<", group(&soft_block_indent(&self.type_annotation())), ">",]);
        });

        if break_after_cast {
            let format_cast = format_cast.memoized();
            let format_expression = self.expression().memoized();

            write!(
                f,
                [best_fitting![
                    format_args!(format_cast, format_expression),
                    format_args!(
                        format_cast,
                        group(&format_args!(
                            token("("),
                            block_indent(&format_expression),
                            token(")")
                        ))
                    ),
                    format_args!(format_cast, format_expression)
                ]]
            );
        } else {
            write!(f, [format_cast, self.expression()]);
        }
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSNonNullExpression<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, [self.expression(), "!"]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, TSInstantiationExpression<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, [self.expression(), self.type_arguments()]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, JSDocNullableType<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        if self.postfix() {
            write!(f, [self.type_annotation(), "?"]);
        } else {
            write!(f, ["?", self.type_annotation()]);
        }
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, JSDocNonNullableType<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        if self.postfix() {
            write!(f, [self.type_annotation(), "!"]);
        } else {
            write!(f, ["!", self.type_annotation()]);
        }
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, JSDocUnknownType> {
    fn write(&self, _f: &mut Formatter<'_, 'a>) {}
}

impl<'a> FormatWrite<'a> for AstNode<'a, StructStatement<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let decorators = self.decorators();
        let id = self.id();
        let type_parameters = self.type_parameters();
        let body = self.body();
        let is_declare = self.declare;

        // Decorators are handled differently depending on the parent context
        // When the struct is exported, the export statement handles decorator formatting
        // to ensure proper placement relative to the export keyword
        if !matches!(
            self.parent,
            AstNodes::ExportNamedDeclaration(_) | AstNodes::ExportDefaultDeclaration(_)
        ) {
            // For non-exported structs, format decorators normally
            write!(f, decorators);
        }

        if is_declare {
            write!(f, ["declare", space()]);
        }

        write!(f, ["struct", space(), id]);

        if let Some(type_parameters) = type_parameters {
            write!(f, type_parameters);
        }

        write!(f, [space(), body]);
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, StructBody<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        write!(f, ["{", block_indent(&self.body()), "}"]);
    }
}

impl<'a> Format<'a> for AstNode<'a, Vec<'a, StructElement<'a>>> {
    fn fmt(&self, f: &mut Formatter<'_, 'a>) {
        // Join struct elements with hard line breaks between them
        let mut join = f.join_nodes_with_hardline();
        // Iterate through pairs of consecutive elements to handle semicolons properly
        // Use the same pattern as ClassElement - iter.peek().copied() should work
        let mut iter = self.iter().peekable();
        while let Some(element) = iter.next() {
            join.entry(element.span(), &(element, iter.peek().copied()));
        }
    }
}

// Helper struct for formatting StructElement with semicolon handling
struct FormatStructElementWithSemicolon<'a, 'b> {
    element: &'b AstNode<'a, StructElement<'a>>,
    next_element: Option<&'b AstNode<'a, StructElement<'a>>>,
}

impl<'a, 'b> FormatStructElementWithSemicolon<'a, 'b> {
    fn new(
        element: &'b AstNode<'a, StructElement<'a>>,
        next_element: Option<&'b AstNode<'a, StructElement<'a>>>,
    ) -> Self {
        Self { element, next_element }
    }

    fn needs_semicolon(&self) -> bool {
        let Self { element, next_element, .. } = self;

        if let StructElement::PropertyDefinition(def) = element.as_ref()
            && def.value.is_none()
            && def.type_annotation.is_none()
        {
            return true;
        }

        let Some(next_element) = next_element else { return false };
        matches!(
            (element.as_ref(), next_element.as_ref()),
            (StructElement::PropertyDefinition(_), StructElement::PropertyDefinition(_))
                | (StructElement::PropertyDefinition(_), StructElement::MethodDefinition(_))
        )
    }
}

impl<'a> Format<'a> for FormatStructElementWithSemicolon<'a, '_> {
    fn fmt(&self, f: &mut Formatter<'_, 'a>) {
        let needs_semi = matches!(self.element.as_ref(), StructElement::PropertyDefinition(_));

        let needs_semi = needs_semi
            && match f.options().semicolons {
                Semicolons::Always => true,
                Semicolons::AsNeeded => self.needs_semicolon(),
            };

        if needs_semi {
            write!(f, [FormatNodeWithoutTrailingComments(self.element), ";"]);
            // Print trailing comments after the semicolon
            match self.element.as_ast_nodes() {
                AstNodes::PropertyDefinition(prop) => {
                    prop.format_trailing_comments(f);
                }
                _ => {}
            }
        } else {
            self.element.fmt(f);
        }
    }
}

impl<'a> Format<'a> for (&AstNode<'a, StructElement<'a>>, Option<&AstNode<'a, StructElement<'a>>>) {
    fn fmt(&self, f: &mut Formatter<'_, 'a>) {
        FormatStructElementWithSemicolon::new(self.0, self.1).fmt(f);
    }
}

/// Helper to format ArkUI chain expressions (like `.onClick(...)`) without the object
/// The `prev_end` parameter specifies the end position of the previous chain/component,
/// used to limit comment search to only the gap between chains.
struct FormatArkUIChainExpression<'a, 'b> {
    chain: &'b AstNode<'a, CallExpression<'a>>,
    prev_end: u32,
}

impl<'a, 'b> FormatArkUIChainExpression<'a, 'b> {
    fn new(chain: &'b AstNode<'a, CallExpression<'a>>, prev_end: u32) -> Self {
        Self { chain, prev_end }
    }
}

impl<'a> Format<'a> for FormatArkUIChainExpression<'a, '_> {
    fn fmt(&self, f: &mut Formatter<'_, 'a>) {
        let chain_expr = self.chain;
        let callee = chain_expr.callee();

        // Format the member access part (e.g., `.onClick`) and call arguments
        match callee.as_ref() {
            Expression::StaticMemberExpression(member) => {
                // Format just the `.property` part without the object
                // Access fields directly since member is a Box<StaticMemberExpression>
                // Format the property name directly as text
                let property_text = text_without_whitespace(member.property.name.as_str());

                // Only get comments between the previous chain's end and this chain's callee start
                // (the dot position). This prevents picking up comments from unrelated parts.
                // Note: We use member.span.start which is typically at the object start, but since
                // the object is the previous chain, we need to find where the dot is.
                // The member.property.span.start is the identifier start, which is after the dot.
                // To be safe, we use the minimum of prev_end+1 and property.span.start-1 as the search end.
                // This ensures we only pick up comments that are truly between chains.
                let search_end = if member.property.span.start > self.prev_end {
                    member.property.span.start
                } else {
                    // Fallback: no gap for comments
                    self.prev_end
                };

                let leading_comments = if search_end > self.prev_end {
                    f.context().comments().comments_in_range(self.prev_end, search_end)
                } else {
                    &[]
                };

                // Use line_suffix_boundary to allow breaking before the dot
                write!(
                    f,
                    [
                        line_suffix_boundary(),
                        FormatLeadingComments::Comments(leading_comments),
                        member.optional.then_some("?"),
                        ".",
                        property_text
                    ]
                );
                // Note: Skip trailing comments between property and arguments for chain expressions
                // to avoid incorrectly picking up comments from other parts of the code.
                // Chain expression arguments immediately follow the property name.

                // Format call arguments
                write!(
                    f,
                    [
                        chain_expr.optional().then_some("?."),
                        chain_expr.type_arguments(),
                        chain_expr.arguments()
                    ]
                );
            }
            Expression::ComputedMemberExpression(_member) => {
                // For computed member expressions, we can't easily format just the member part
                // without the object due to lifetime constraints. Fall back to formatting
                // the entire call expression, which may cause some duplication but is better
                // than a compilation error. In practice, ArkUI chain expressions typically
                // use static member expressions (like .onClick), so this case is rare.
                write!(f, chain_expr);
            }
            _ => {
                // Fallback: format the entire call expression
                write!(f, chain_expr);
            }
        }
    }
}

/// Check if ArkUI chain expressions should break into multiple lines
fn should_break_arkui_chain(
    chain_expressions: &[CallExpression<'_>],
    _f: &Formatter<'_, '_>,
) -> bool {
    if chain_expressions.len() > 1 {
        return true;
    }

    // Check if any chain expression has complex arguments (arrow functions, function expressions, etc.)
    for chain_expr in chain_expressions.iter() {
        // Check the arguments directly from the CallExpression
        let arguments = &chain_expr.arguments;
        if arguments.len() > 0 {
            // Check if any argument is an arrow function or function expression
            for arg in arguments.iter() {
                match arg {
                    Argument::ArrowFunctionExpression(_) | Argument::FunctionExpression(_) => {
                        return true;
                    }
                    _ => {
                        // Check if the argument is a complex expression (object, array, etc.)
                        if let Some(expr) = arg.as_expression() {
                            match expr {
                                Expression::ObjectExpression(_)
                                | Expression::ArrayExpression(_) => {
                                    return true;
                                }
                                _ => {}
                            }
                        }
                    }
                }
            }
        }
    }

    false
}

/// Find the span of the children block content for an ArkUI component.
/// Returns a Span from after `{` to before `}` if a children block exists, or None if there's no block.
///
/// The structure of an ArkUI component is:
/// ```arkui
/// Component() {  // <- arguments, then children start
///   Child()      // <- children content
/// }              // <- children end
/// .method()      // <- chain expressions
/// ```
fn find_arkui_children_block_span(
    arkui_expr: &ArkUIComponentExpression<'_>,
    source_text: &str,
) -> Option<oxc_span::Span> {
    // Children block comes AFTER arguments but BEFORE chain expressions
    // Find where to start searching - after arguments close paren
    let search_start = if let Some(last_arg) = arkui_expr.arguments.last() {
        last_arg.span().end
    } else if let Some(type_args) = &arkui_expr.type_arguments {
        type_args.span.end
    } else {
        arkui_expr.callee.span().end
    };

    // Find where to stop searching - before chain expressions or at component span end
    let search_end = if let Some(first_chain) = arkui_expr.chain_expressions.first() {
        first_chain.span.start
    } else {
        arkui_expr.span.end
    };

    // Safety check: ensure valid range
    if search_start >= search_end {
        return None;
    }

    // Search for `{` and `}` in source text to get the block span
    let search_range = &source_text[search_start as usize..search_end as usize];
    let mut block_start: Option<u32> = None;
    let mut block_end: Option<u32> = None;

    for (i, byte) in search_range.bytes().enumerate() {
        let pos = search_start + i as u32;
        match byte {
            b'{' if block_start.is_none() => {
                // Found the opening brace - content starts after it
                block_start = Some(pos + 1);
            }
            b'}' if block_start.is_some() => {
                // Found the closing brace - content ends before it
                block_end = Some(pos);
                break;
            }
            b' ' | b'\t' | b'\n' | b'\r' | b')' if block_start.is_none() => {
                // Skip whitespace and closing paren before finding `{`
                continue;
            }
            _ if block_start.is_none() => {
                // Some other character before `{` - not a children block
                return None;
            }
            _ => {
                // Inside the block, continue looking for `}`
                continue;
            }
        }
    }

    match (block_start, block_end) {
        (Some(start), Some(end)) => Some(oxc_span::Span::new(start, end)),
        _ => None,
    }
}

impl<'a> FormatWrite<'a> for AstNode<'a, ArkUIComponentExpression<'a>> {
    fn write(&self, f: &mut Formatter<'_, 'a>) {
        let callee = self.callee();
        let type_arguments = self.type_arguments();
        let arguments = self.arguments();
        let children = self.children();
        let chain_expressions = self.chain_expressions();

        // Format callee
        write!(f, [FormatNodeWithoutTrailingComments(callee)]);

        // Format type arguments if present
        if let Some(type_arguments) = type_arguments {
            write!(f, type_arguments);
        }

        // Format arguments
        // Note: arguments already formats itself with parentheses, so we don't add extra ones
        write!(f, [arguments]);

        // Format children block
        // We need to check source text to determine if there's a `{...}` block,
        // because children Vec can be empty even when there's a block with only comments
        if !children.as_ref().is_empty() {
            write!(f, [space(), "{", block_indent(&children), "}"]);
        } else if let Some(block_span) =
            find_arkui_children_block_span(self.as_ref(), f.source_text().as_ref())
        {
            // Empty children block - handle dangling comments inside
            write!(
                f,
                [space(), "{", format_dangling_comments(block_span).with_block_indent(), "}"]
            );
        }

        // Format chain expressions
        // Use a helper to format only the member and call parts, not the object
        // Support line breaks when the chain is too long
        if !chain_expressions.as_ref().is_empty() {
            let should_break = should_break_arkui_chain(chain_expressions.as_ref(), f);
            let has_children = !children.as_ref().is_empty();

            // Calculate the starting position for the first chain expression's comment search
            // This should be after the children block or arguments
            let initial_prev_end = if !children.as_ref().is_empty() {
                // After children block - find the end of last child
                children.as_ref().last().map(|c| c.span().end).unwrap_or(self.span.start)
            } else if let Some(block_span) =
                find_arkui_children_block_span(self.as_ref(), f.source_text().as_ref())
            {
                // Empty children block - use block span end
                block_span.end
            } else if let Some(last_arg) = self.arguments.last() {
                // No children block - use end of arguments
                last_arg.span().end
            } else {
                // No arguments - use callee end or span start
                self.callee.span().end
            };

            // Collect chain refs for iteration
            let chain_refs: std::vec::Vec<_> = chain_expressions.iter().collect();

            if should_break {
                // Force multi-line format when chain should break
                // If component has children ({}), chain expressions align with component (no indent)
                // If component has no children, chain expressions should be indented
                let format_chains_multi_line = format_with(|f| {
                    let mut prev_end = initial_prev_end;
                    for (i, chain_expr_node) in chain_refs.iter().enumerate() {
                        if i > 0 {
                            write!(f, [hard_line_break()]);
                        }
                        write!(f, [FormatArkUIChainExpression::new(chain_expr_node, prev_end)]);
                        prev_end = chain_expr_node.span.end;
                    }
                });
                // Add a line break before the first chain expression
                // If component has children, no indentation (aligned with component)
                // If component has no children, add indentation
                if has_children {
                    write!(f, [hard_line_break(), format_chains_multi_line]);
                } else {
                    write!(f, [indent(&format_args!(hard_line_break(), format_chains_multi_line))]);
                }
            } else {
                // Format all chain expressions, allowing breaking when needed
                // In single-line format, chain expressions should be directly connected (no space)
                let format_chains_single_line = format_with(|f| {
                    let mut prev_end = initial_prev_end;
                    for chain_expr_node in chain_refs.iter() {
                        write!(f, [FormatArkUIChainExpression::new(chain_expr_node, prev_end)]);
                        prev_end = chain_expr_node.span.end;
                    }
                });

                // In multi-line format, each chain expression should be on a new line
                // If component has children, no indentation (aligned with component)
                // If component has no children, add indentation
                let format_chains_multi_line = format_with(|f| {
                    let mut prev_end = initial_prev_end;
                    for (i, chain_expr_node) in chain_refs.iter().enumerate() {
                        if i > 0 {
                            write!(f, [hard_line_break()]);
                        }
                        write!(f, [FormatArkUIChainExpression::new(chain_expr_node, prev_end)]);
                        prev_end = chain_expr_node.span.end;
                    }
                });

                // Use best_fitting to choose between single-line and multi-line formatting
                // This allows the formatter to break the chain when it's too long
                // Wrap in a group to allow breaking when needed
                // If component has children, chain expressions align with component (no indent)
                // If component has no children, chain expressions should be indented
                let format_content = format_with(|f| {
                    if has_children {
                        write!(
                            f,
                            [best_fitting!(
                                format_chains_single_line,
                                format_args!(hard_line_break(), format_chains_multi_line)
                            )]
                        );
                    } else {
                        write!(
                            f,
                            [best_fitting!(
                                format_chains_single_line,
                                indent(&format_args!(hard_line_break(), format_chains_multi_line))
                            )]
                        );
                    }
                });
                write!(f, [group(&format_content)]);
            }
        }
    }
}

impl<'a> Format<'a> for AstNode<'a, Vec<'a, ArkUIChild<'a>>> {
    fn fmt(&self, f: &mut Formatter<'_, 'a>) {
        let mut join = f.join_nodes_with_hardline();
        for child in self.iter() {
            join.entry(child.span(), child);
        }
    }
}
