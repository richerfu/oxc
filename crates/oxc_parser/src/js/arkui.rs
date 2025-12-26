//! ArkUI parsing functions
//!
//! This module contains parsing logic for HarmonyOS ArkUI syntax including:
//! - Struct declarations (`struct ComponentName { ... }`)
//! - ArkUI component expressions (`Column() { ... }`)

use oxc_allocator::{Box, CloneIn, Vec};
use oxc_ast::{NONE, ast::*};
use oxc_span::Span;

use crate::{
    Context, ParserImpl, StatementContext, diagnostics,
    lexer::Kind,
    modifiers::{ModifierFlags, ModifierKind, Modifiers},
};

use super::FunctionKind;

impl<'a> ParserImpl<'a> {
    /// Parse a struct statement
    ///
    /// ## Example
    /// ```arkui
    /// @Component
    /// struct MyComponent {
    ///   @State message: string = 'Hello';
    ///   build() {
    ///     Column() {}
    ///   }
    /// }
    /// ```
    pub(crate) fn parse_struct_statement(
        &mut self,
        start_span: u32,
        stmt_ctx: StatementContext,
        modifiers: &Modifiers<'a>,
        decorators: Vec<'a, Decorator<'a>>,
    ) -> Statement<'a> {
        let decl = self.parse_struct_declaration(start_span, modifiers, decorators);
        if stmt_ctx.is_single_statement() {
            self.error(diagnostics::class_declaration(Span::new(
                decl.span.start,
                decl.body.span.start,
            )));
        }
        Statement::StructStatement(decl)
    }

    /// Parse a struct declaration
    pub(crate) fn parse_struct_declaration(
        &mut self,
        start_span: u32,
        modifiers: &Modifiers<'a>,
        decorators: Vec<'a, Decorator<'a>>,
    ) -> Box<'a, StructStatement<'a>> {
        self.bump_any(); // advance `struct`

        // Move span start to decorator position if decorators exist
        let mut start_span = start_span;
        if let Some(d) = decorators.first() {
            start_span = d.span.start;
        }

        let id = if self.cur_kind().is_binding_identifier() {
            self.parse_binding_identifier()
        } else {
            self.unexpected()
        };

        let type_parameters = if self.is_ts { self.parse_ts_type_parameters() } else { None };
        let body = self.parse_struct_body();

        self.verify_modifiers(
            modifiers,
            ModifierFlags::DECLARE | ModifierFlags::ABSTRACT,
            true,
            diagnostics::modifier_cannot_be_used_here,
        );

        let span = self.end_span(start_span);

        let declare = modifiers.contains(ModifierKind::Declare);

        self.ast.alloc_struct_statement(span, decorators, id, type_parameters, body, declare)
    }

    /// Parse struct body containing properties and methods
    fn parse_struct_body(&mut self) -> Box<'a, StructBody<'a>> {
        let span = self.start_span();
        let struct_elements = self.parse_normal_list_breakable(Kind::LCurly, Kind::RCurly, |p| {
            // Skip empty struct element `;`
            if p.eat(Kind::Semicolon) {
                while p.eat(Kind::Semicolon) {
                    // consume multiple semicolons
                }
                if p.at(Kind::RCurly) {
                    return None;
                }
            }
            Some(Self::parse_struct_element(p))
        });
        self.ast.alloc_struct_body(self.end_span(span), struct_elements)
    }

    /// Parse a struct element (property or method)
    fn parse_struct_element(&mut self) -> StructElement<'a> {
        let span = self.start_span();

        let decorators = self.parse_decorators();
        let modifiers = self.parse_modifiers(
            /* permit_const_as_modifier */ true,
            /* stop_on_start_of_class_static_block */ false,
        );

        self.verify_modifiers(
            &modifiers,
            !ModifierFlags::EXPORT,
            false,
            diagnostics::cannot_appear_on_class_elements,
        );

        // Check for get/set accessors (similar to class elements)
        let r#abstract = modifiers.contains(ModifierKind::Abstract);
        let r#type = if r#abstract {
            MethodDefinitionType::TSAbstractMethodDefinition
        } else {
            MethodDefinitionType::MethodDefinition
        };

        if self.parse_contextual_modifier(Kind::Get) {
            return StructElement::MethodDefinition(self.parse_struct_accessor_declaration(
                span,
                r#type,
                MethodDefinitionKind::Get,
                &modifiers,
                decorators,
            ));
        }

        if self.parse_contextual_modifier(Kind::Set) {
            return StructElement::MethodDefinition(self.parse_struct_accessor_declaration(
                span,
                r#type,
                MethodDefinitionKind::Set,
                &modifiers,
                decorators,
            ));
        }

        // Parse property or method declaration (similar to class)
        if self.cur_kind().is_identifier_or_keyword()
            || self.at(Kind::Star)
            || self.at(Kind::LBrack)
        {
            return self.parse_property_or_method_declaration_for_struct(
                span, r#type, &modifiers, decorators,
            );
        }

        // Otherwise parse as property definition
        self.parse_property_definition_for_struct(span, &modifiers, decorators)
    }

    /// Parse property or method declaration for struct (similar to class)
    fn parse_property_or_method_declaration_for_struct(
        &mut self,
        span: u32,
        r#type: MethodDefinitionType,
        modifiers: &Modifiers<'a>,
        decorators: Vec<'a, Decorator<'a>>,
    ) -> StructElement<'a> {
        let generator = self.eat(Kind::Star);
        let (name, computed) = self.parse_property_name();

        // Handle optional ? token (aligned with class parsing)
        let cur_token = self.cur_token();
        let optional_span = (cur_token.kind() == Kind::Question).then(|| {
            let span = cur_token.span();
            self.bump_any();
            span
        });
        let optional = optional_span.is_some();

        // Check if this is a method (generator or has parentheses or type parameters)
        if generator || matches!(self.cur_kind(), Kind::LParen | Kind::LAngle) {
            return StructElement::MethodDefinition(self.parse_method_declaration_for_struct(
                span, r#type, generator, name, computed, optional, modifiers, decorators,
            ));
        }

        // Otherwise parse as property
        let definite = self.eat(Kind::Bang);

        if definite && let Some(optional_span) = optional_span {
            self.error(diagnostics::optional_definite_property(optional_span.expand_right(1)));
        }

        self.parse_property_declaration_for_struct(
            span,
            name,
            computed,
            optional_span,
            definite,
            modifiers,
            decorators,
        )
    }

    /// Parse method declaration for struct (similar to class)
    fn parse_method_declaration_for_struct(
        &mut self,
        span: u32,
        r#type: MethodDefinitionType,
        generator: bool,
        name: PropertyKey<'a>,
        computed: bool,
        optional: bool,
        modifiers: &Modifiers<'a>,
        decorators: Vec<'a, Decorator<'a>>,
    ) -> Box<'a, MethodDefinition<'a>> {
        let value = self.parse_method(
            modifiers.contains(ModifierKind::Async),
            generator,
            FunctionKind::ClassMethod,
        );
        self.ast.alloc_method_definition(
            self.end_span(span),
            r#type,
            decorators,
            name,
            value,
            MethodDefinitionKind::Method,
            computed,
            modifiers.contains(ModifierKind::Static),
            modifiers.contains(ModifierKind::Override),
            optional,
            modifiers.accessibility(),
        )
    }

    /// Parse property declaration for struct (similar to class)
    fn parse_property_declaration_for_struct(
        &mut self,
        span: u32,
        name: PropertyKey<'a>,
        computed: bool,
        optional_span: Option<Span>,
        definite: bool,
        modifiers: &Modifiers<'a>,
        decorators: Vec<'a, Decorator<'a>>,
    ) -> StructElement<'a> {
        let optional = optional_span.is_some();

        // Parse optional type annotation
        let type_annotation = if self.is_ts && self.eat(Kind::Colon) {
            let span = self.start_span();
            let ts_type = self.parse_ts_type();
            Some(self.ast.alloc_ts_type_annotation(self.end_span(span), ts_type))
        } else {
            None
        };

        // Parse optional initializer
        let initializer = self
            .eat(Kind::Eq)
            .then(|| self.context(Context::In, Context::Yield | Context::Await, Self::parse_expr));

        // Semicolon is optional in struct bodies
        let _ = self.eat(Kind::Semicolon);

        let r#type = PropertyDefinitionType::PropertyDefinition;
        let property_def = self.ast.alloc_property_definition(
            self.end_span(span),
            r#type,
            decorators,
            name,
            type_annotation,
            initializer,
            computed,
            modifiers.contains(ModifierKind::Static),
            false, // declare
            modifiers.contains(ModifierKind::Override),
            optional,
            definite,
            modifiers.contains(ModifierKind::Readonly),
            modifiers.accessibility(),
        );

        StructElement::PropertyDefinition(property_def)
    }

    /// Parse an accessor declaration (get/set) for struct
    fn parse_struct_accessor_declaration(
        &mut self,
        span: u32,
        r#type: MethodDefinitionType,
        kind: MethodDefinitionKind,
        modifiers: &Modifiers<'a>,
        decorators: Vec<'a, Decorator<'a>>,
    ) -> Box<'a, MethodDefinition<'a>> {
        let (name, computed) = self.parse_property_name();
        let value = self.parse_method(
            modifiers.contains(ModifierKind::Async),
            false,
            FunctionKind::ClassMethod,
        );
        let method_definition = self.ast.alloc_method_definition(
            self.end_span(span),
            r#type,
            decorators,
            name,
            value,
            kind,
            computed,
            modifiers.contains(ModifierKind::Static),
            modifiers.contains(ModifierKind::Override),
            false,
            modifiers.accessibility(),
        );
        match kind {
            MethodDefinitionKind::Get => self.check_getter(&method_definition.value),
            MethodDefinitionKind::Set => self.check_setter(&method_definition.value),
            _ => {}
        }
        self.verify_modifiers(
            modifiers,
            !(ModifierFlags::ASYNC | ModifierFlags::DECLARE),
            false,
            diagnostics::modifier_cannot_be_used_here,
        );
        method_definition
    }

    /// Parse a property definition for struct (fallback when not identifier/keyword/star/bracket)
    fn parse_property_definition_for_struct(
        &mut self,
        span: u32,
        modifiers: &Modifiers<'a>,
        decorators: Vec<'a, Decorator<'a>>,
    ) -> StructElement<'a> {
        // Parse property key
        let (name, computed) = self.parse_property_name();
        let optional_span = (self.cur_token().kind() == Kind::Question).then(|| {
            let span = self.cur_token().span();
            self.bump_any();
            span
        });
        let definite = self.eat(Kind::Bang);

        if definite && let Some(optional_span) = optional_span {
            self.error(diagnostics::optional_definite_property(optional_span.expand_right(1)));
        }

        self.parse_property_declaration_for_struct(
            span,
            name,
            computed,
            optional_span,
            definite,
            modifiers,
            decorators,
        )
    }

    /// Parse an ArkUI component expression
    ///
    /// ## Example
    /// ```arkui
    /// Column() {
    ///   Text('Hello')
    ///   Button('Click')
    /// }
    /// ```
    pub(crate) fn parse_arkui_component_expression(
        &mut self,
        callee: Expression<'a>,
    ) -> Expression<'a> {
        let span = self.start_span();

        // Parse type arguments if present (for generic components)
        let type_arguments = if self.is_ts { self.try_parse_type_arguments() } else { None };

        // Parse arguments
        let opening_span = self.cur_token().span();
        self.expect(Kind::LParen);
        let (exprs, _) = self.parse_delimited_list(
            Kind::RParen,
            Kind::Comma,
            opening_span,
            Self::parse_assignment_expression_or_higher,
        );
        let mut arguments = self.ast.vec();
        for expr in exprs {
            arguments.push(Argument::from(expr));
        }
        self.expect(Kind::RParen);

        // Parse children block if present
        let children = if self.eat(Kind::LCurly) {
            let mut children_vec = self.ast.vec();
            while !self.at(Kind::RCurly) && !self.has_fatal_error() {
                // Parse child element
                let child = self.parse_arkui_child();
                children_vec.push(child);

                // Optional semicolon between children
                let _ = self.eat(Kind::Semicolon);
            }
            self.expect(Kind::RCurly);
            children_vec
        } else {
            self.ast.vec()
        };

        // Create the component expression first (without chain expressions)
        // We'll add chain expressions after, and they'll reference this component expression
        let component_expr =
            Expression::ArkUIComponentExpression(self.ast.alloc_ark_ui_component_expression(
                self.end_span(span),
                callee,
                type_arguments,
                arguments,
                children,
                self.ast.vec(), // chain_expressions will be added below
            ));

        // Parse chain expressions (like .onClick(...))
        // Chain expressions are stored in the component expression's chain_expressions field
        let mut chain_expressions = self.ast.vec();
        while self.eat(Kind::Dot) {
            if self.cur_kind().is_identifier_or_keyword() {
                let ident_span = self.start_span();
                let ident = self.parse_identifier_name();
                if self.at(Kind::LParen) {
                    // Create member expression pointing to the component expression
                    let member_expr = self.ast.member_expression_static(
                        self.end_span(ident_span),
                        component_expr.clone_in(self.ast.allocator),
                        ident,
                        false,
                    );
                    // Parse call arguments
                    let call_span = self.start_span();
                    let opening_span = self.cur_token().span();
                    self.expect(Kind::LParen);
                    let (exprs, _) = self.parse_delimited_list(
                        Kind::RParen,
                        Kind::Comma,
                        opening_span,
                        Self::parse_assignment_expression_or_higher,
                    );
                    let mut call_args = self.ast.vec();
                    for expr in exprs {
                        call_args.push(Argument::from(expr));
                    }
                    self.expect(Kind::RParen);
                    // Create call expression
                    let call_expr_expr = self.ast.expression_call(
                        self.end_span(call_span),
                        Expression::from(member_expr),
                        NONE,
                        call_args,
                        false,
                    );
                    // Extract CallExpression from Expression
                    if let Expression::CallExpression(call_expr_box) = call_expr_expr {
                        // Clone CallExpression from the box
                        chain_expressions.push(call_expr_box.as_ref().clone_in(self.ast.allocator));
                    } else {
                        unreachable!("expression_call should return CallExpression");
                    }
                } else {
                    // Not a call expression, break
                    break;
                }
            } else {
                break;
            }
        }

        // Update the component expression to include chain expressions
        // Extract fields from the existing component expression and create a new one with chain expressions
        if let Expression::ArkUIComponentExpression(component) = component_expr {
            Expression::ArkUIComponentExpression(self.ast.alloc_ark_ui_component_expression(
                component.span,
                component.callee.clone_in(self.ast.allocator),
                component.type_arguments.clone_in(self.ast.allocator),
                component.arguments.clone_in(self.ast.allocator),
                component.children.clone_in(self.ast.allocator),
                chain_expressions,
            ))
        } else {
            unreachable!("component_expr should be ArkUIComponentExpression")
        }
    }

    /// Parse an ArkUI component expression after arguments have been parsed
    pub(crate) fn parse_arkui_component_expression_after_args(
        &mut self,
        span: u32,
        callee: Expression<'a>,
        type_arguments: Option<Box<'a, TSTypeParameterInstantiation<'a>>>,
        arguments: Vec<'a, Argument<'a>>,
    ) -> Expression<'a> {
        // Parse children block
        let children = if self.eat(Kind::LCurly) {
            let mut children_vec = self.ast.vec();
            while !self.at(Kind::RCurly) && !self.has_fatal_error() {
                // Parse child element
                let child = self.parse_arkui_child();
                children_vec.push(child);

                // Optional semicolon between children
                let _ = self.eat(Kind::Semicolon);
            }
            self.expect(Kind::RCurly);
            children_vec
        } else {
            self.ast.vec()
        };

        // Create the component expression first (without chain expressions)
        // We'll add chain expressions after, and they'll reference this component expression
        let component_expr =
            Expression::ArkUIComponentExpression(self.ast.alloc_ark_ui_component_expression(
                self.end_span(span),
                callee,
                type_arguments,
                arguments,
                children,
                self.ast.vec(), // chain_expressions will be added below
            ));

        // Parse chain expressions (like .onClick(...))
        // Chain expressions are stored in the component expression's chain_expressions field
        let mut chain_expressions = self.ast.vec();
        while self.eat(Kind::Dot) {
            if self.cur_kind().is_identifier_or_keyword() {
                let ident_span = self.start_span();
                let ident = self.parse_identifier_name();
                if self.at(Kind::LParen) {
                    // Create member expression pointing to the component expression
                    let member_expr = self.ast.member_expression_static(
                        self.end_span(ident_span),
                        component_expr.clone_in(self.ast.allocator),
                        ident,
                        false,
                    );
                    // Parse call arguments
                    let call_span = self.start_span();
                    let opening_span = self.cur_token().span();
                    self.expect(Kind::LParen);
                    let (exprs, _) = self.parse_delimited_list(
                        Kind::RParen,
                        Kind::Comma,
                        opening_span,
                        Self::parse_assignment_expression_or_higher,
                    );
                    let mut call_args = self.ast.vec();
                    for expr in exprs {
                        call_args.push(Argument::from(expr));
                    }
                    self.expect(Kind::RParen);
                    // Create call expression
                    let call_expr_expr = self.ast.expression_call(
                        self.end_span(call_span),
                        Expression::from(member_expr),
                        NONE,
                        call_args,
                        false,
                    );
                    // Extract CallExpression from Expression
                    if let Expression::CallExpression(call_expr_box) = call_expr_expr {
                        // Clone CallExpression from the box
                        chain_expressions.push(call_expr_box.as_ref().clone_in(self.ast.allocator));
                    } else {
                        unreachable!("expression_call should return CallExpression");
                    }
                } else {
                    // Not a call expression, break
                    break;
                }
            } else {
                break;
            }
        }

        // Update the component expression to include chain expressions
        // Extract fields from the existing component expression and create a new one with chain expressions
        if let Expression::ArkUIComponentExpression(component) = component_expr {
            Expression::ArkUIComponentExpression(self.ast.alloc_ark_ui_component_expression(
                component.span,
                component.callee.clone_in(self.ast.allocator),
                component.type_arguments.clone_in(self.ast.allocator),
                component.arguments.clone_in(self.ast.allocator),
                component.children.clone_in(self.ast.allocator),
                chain_expressions,
            ))
        } else {
            unreachable!("component_expr should be ArkUIComponentExpression")
        }
    }

    /// Parse an ArkUI child element
    fn parse_arkui_child(&mut self) -> ArkUIChild<'a> {
        // Check for control flow statements first (if, for, while, switch, etc.)
        // These are commonly used in ArkUI children for conditional rendering
        match self.cur_kind() {
            Kind::If
            | Kind::For
            | Kind::While
            | Kind::Do
            | Kind::Switch
            | Kind::Try
            | Kind::With
            | Kind::Break
            | Kind::Continue
            | Kind::Return
            | Kind::Throw
            | Kind::Debugger => {
                // Parse as statement
                let stmt = self.parse_statement_list_item(StatementContext::StatementList);
                return ArkUIChild::Statement(self.alloc(stmt));
            }
            _ => {}
        }

        // Check if this is another component expression
        if self.cur_kind().is_identifier_or_keyword() {
            let checkpoint = self.checkpoint();
            let ident_expr = self.parse_identifier_expression();

            if self.at(Kind::LParen) {
                // This is a component expression
                let component_expr = self.parse_arkui_component_expression(ident_expr);
                if let Expression::ArkUIComponentExpression(expr) = component_expr {
                    return ArkUIChild::Component(expr);
                } else {
                    unreachable!(
                        "parse_arkui_component_expression should return ArkUIComponentExpression"
                    );
                }
            } else {
                // Not a component, restore and parse as regular expression
                self.rewind(checkpoint);
            }
        }

        // Parse as regular expression
        let expr = self.parse_assignment_expression_or_higher();
        ArkUIChild::Expression(self.alloc(expr))
    }
}
