use oxc_allocator::Box;
use oxc_ast::ast::*;
use oxc_syntax::operator::AssignmentOperator;

use crate::{
    Context, ParserImpl, diagnostics,
    lexer::Kind,
    modifiers::{ModifierFlags, Modifiers},
};

use super::FunctionKind;

impl<'a> ParserImpl<'a> {
    /// [Object Expression](https://tc39.es/ecma262/#sec-object-initializer)
    /// `ObjectLiteral`[Yield, Await] :
    ///     { }
    ///     { `PropertyDefinitionList`[?Yield, ?Await] }
    ///     { `PropertyDefinitionList`[?Yield, ?Await] , }
    pub(crate) fn parse_object_expression(&mut self) -> Box<'a, ObjectExpression<'a>> {
        let span = self.start_span();
        let opening_span = self.cur_token().span();
        self.expect(Kind::LCurly);

        // Check if this is an ArkUI object literal with expression statements (e.g., { .backgroundColor(...) })
        // In ArkUI, object literals can contain expression statements starting with dots
        if self.source_type.is_arkui() && self.at(Kind::Dot) {
            // Parse as ArkUI object literal with expression statements
            return self.parse_arkui_object_expression_with_statements(span, opening_span);
        }

        let (object_expression_properties, comma_span) = self.context_add(Context::In, |p| {
            p.parse_delimited_list(
                Kind::RCurly,
                Kind::Comma,
                opening_span,
                Self::parse_object_expression_property,
            )
        });
        if let Some(comma_span) = comma_span {
            self.state.trailing_commas.insert(span, self.end_span(comma_span));
        }
        self.expect(Kind::RCurly);
        self.ast.alloc_object_expression(self.end_span(span), object_expression_properties)
    }

    /// Parse ArkUI object literal with expression statements
    /// Example: { .backgroundColor('#ffffeef0') }
    /// In ArkUI, object literals can contain expression statements starting with dots
    fn parse_arkui_object_expression_with_statements(
        &mut self,
        span: u32,
        _opening_span: Span,
    ) -> Box<'a, ObjectExpression<'a>> {
        use crate::lexer::Kind;
        let mut properties = self.ast.vec();

        // Parse expression statements until closing brace
        while !self.at(Kind::RCurly) && !self.has_fatal_error() {
            if self.at(Kind::Dot) {
                // Parse expression statement starting with dot as LeadingDotMemberExpression
                // Allow chaining (e.g., .borderRadius(20).borderWidth(1)) - it will stop at comma/semicolon/brace
                let expr_span = self.start_span();
                let expr = self.parse_leading_dot_expression(true);
                let expr_end_span = self.end_span(expr_span);

                // Create a property with the expression as value
                // Use a synthetic key for the expression statement
                let key_name = self.ast.identifier_name(expr_end_span, oxc_span::Atom::from(""));
                let key = PropertyKey::StaticIdentifier(self.alloc(key_name));
                let property = self.ast.alloc_object_property(
                    expr_end_span,
                    PropertyKind::Init,
                    key,
                    expr,
                    false, // not a method
                    false, // not shorthand
                    false, // not computed
                );
                properties.push(ObjectPropertyKind::ObjectProperty(property));

                // Optional semicolon or comma (both are allowed after expression statements)
                if self.eat(Kind::Semicolon) {
                    // Semicolon consumed
                } else if self.at(Kind::Comma) {
                    // Comma after expression statement (e.g., .method1().method2(),)
                    self.expect(Kind::Comma);
                }
                // If neither semicolon nor comma, continue to next token (could be closing brace or next property)
            } else {
                // Parse as normal object property
                let property = self.parse_object_expression_property();
                properties.push(property);

                // Expect comma or closing brace
                if !self.at(Kind::RCurly) {
                    self.expect(Kind::Comma);
                }
            }
        }

        self.expect(Kind::RCurly);
        self.ast.alloc_object_expression(self.end_span(span), properties)
    }

    fn parse_object_expression_property(&mut self) -> ObjectPropertyKind<'a> {
        match self.cur_kind() {
            Kind::Dot3 => ObjectPropertyKind::SpreadProperty(self.parse_spread_element()),
            _ => ObjectPropertyKind::ObjectProperty(self.parse_object_literal_element()),
        }
    }

    /// `PropertyDefinition`[Yield, Await]
    fn parse_object_literal_element(&mut self) -> Box<'a, ObjectProperty<'a>> {
        let span = self.start_span();

        let modifiers = self.parse_modifiers(
            /* permit_const_as_modifier */ false,
            /* stop_on_start_of_class_static_block */ false,
        );

        if self.parse_contextual_modifier(Kind::Get) {
            return self.parse_method_getter_setter(span, PropertyKind::Get, &modifiers);
        }

        if self.parse_contextual_modifier(Kind::Set) {
            return self.parse_method_getter_setter(span, PropertyKind::Set, &modifiers);
        }

        let asterisk_token = self.eat(Kind::Star);
        let token_is_identifier =
            self.cur_kind().is_identifier_reference(self.ctx.has_yield(), self.ctx.has_await());
        let (key, computed) = self.parse_property_name();

        if asterisk_token || matches!(self.cur_kind(), Kind::LParen | Kind::LAngle) {
            self.verify_modifiers(
                &modifiers,
                ModifierFlags::ASYNC,
                true,
                diagnostics::modifier_cannot_be_used_here,
            );
            let method = self.parse_method(
                modifiers.contains_async(),
                asterisk_token,
                FunctionKind::ObjectMethod,
            );
            return self.ast.alloc_object_property(
                self.end_span(span),
                PropertyKind::Init,
                key,
                Expression::FunctionExpression(method),
                /* method */ true,
                /* shorthand */ false,
                computed,
            );
        }

        self.verify_modifiers(
            &modifiers,
            ModifierFlags::empty(),
            true,
            diagnostics::modifier_cannot_be_used_here,
        );

        let is_shorthand_property_assignment = token_is_identifier && !self.at(Kind::Colon);

        if is_shorthand_property_assignment {
            if let PropertyKey::StaticIdentifier(identifier_name) = key {
                let identifier_reference =
                    self.ast.identifier_reference(identifier_name.span, identifier_name.name);
                let value = Expression::Identifier(self.alloc(identifier_reference.clone()));
                // CoverInitializedName ({ foo = bar })
                if self.eat(Kind::Eq) {
                    let right = self.parse_assignment_expression_or_higher();
                    let left = AssignmentTarget::AssignmentTargetIdentifier(
                        self.alloc(identifier_reference),
                    );
                    let expr = self.ast.assignment_expression(
                        self.end_span(span),
                        AssignmentOperator::Assign,
                        left,
                        right,
                    );
                    self.state.cover_initialized_name.insert(span, expr);
                }
                self.ast.alloc_object_property(
                    self.end_span(span),
                    PropertyKind::Init,
                    PropertyKey::StaticIdentifier(identifier_name),
                    value,
                    /* method */ false,
                    /* shorthand */ true,
                    computed,
                )
            } else {
                self.unexpected()
            }
        } else {
            self.parse_property_definition_assignment(span, key, computed)
        }
    }

    /// `PropertyDefinition`[Yield, Await] :
    ///   ... `AssignmentExpression`[+In, ?Yield, ?Await]
    pub(crate) fn parse_spread_element(&mut self) -> Box<'a, SpreadElement<'a>> {
        let span = self.start_span();
        self.bump_any(); // advance `...`
        let argument = self.parse_assignment_expression_or_higher();
        self.ast.alloc_spread_element(self.end_span(span), argument)
    }

    /// `PropertyDefinition`[Yield, Await] :
    ///   `PropertyName`[?Yield, ?Await] : `AssignmentExpression`[+In, ?Yield, ?Await]
    fn parse_property_definition_assignment(
        &mut self,
        span: u32,
        key: PropertyKey<'a>,
        computed: bool,
    ) -> Box<'a, ObjectProperty<'a>> {
        self.expect(Kind::Colon);

        // Check if the value is an ArkUI object literal with leading-dot expressions
        // Example: normal: { .borderRadius(20) .borderWidth(1) }
        let value = if self.source_type.is_arkui() && self.at(Kind::LCurly) {
            // Check if after the opening brace, there's a dot
            // We'll parse the opening brace and then check
            let obj_span = self.start_span();
            let opening_span = self.cur_token().span();
            self.expect(Kind::LCurly);

            // Check if next token is Dot (after consuming whitespace)
            if self.at(Kind::Dot) {
                // Parse as ArkUI object literal with expression statements
                // We've already consumed the opening brace, so we need to handle it differently
                let mut properties = self.ast.vec();

                // Parse expression statements until closing brace
                while !self.at(Kind::RCurly) && !self.has_fatal_error() {
                    if self.at(Kind::Dot) {
                        // Parse expression statement starting with dot as LeadingDotMemberExpression
                        // Allow chaining (e.g., .borderRadius(20).borderWidth(1)) - it will stop at comma/semicolon/brace
                        let expr_span = self.start_span();
                        let expr = self.parse_leading_dot_expression(true);
                        let expr_end_span = self.end_span(expr_span);

                        // Create a property with the expression as value
                        // Use a synthetic key for the expression statement
                        let key_name =
                            self.ast.identifier_name(expr_end_span, oxc_span::Atom::from(""));
                        let key = PropertyKey::StaticIdentifier(self.alloc(key_name));
                        let property = self.ast.alloc_object_property(
                            expr_end_span,
                            PropertyKind::Init,
                            key,
                            expr,
                            false, // not a method
                            false, // not shorthand
                            false, // not computed
                        );
                        properties.push(ObjectPropertyKind::ObjectProperty(property));

                        // Optional semicolon or comma (both are allowed after expression statements)
                        if self.eat(Kind::Semicolon) {
                            // Semicolon consumed
                        } else if self.at(Kind::Comma) {
                            // Comma after expression statement (e.g., .method1().method2(),)
                            self.expect(Kind::Comma);
                        }
                        // If neither semicolon nor comma, continue to next token (could be closing brace or next property)
                    } else {
                        // Parse as normal object property
                        let property = self.parse_object_expression_property();
                        properties.push(property);

                        // Expect comma or closing brace
                        if !self.at(Kind::RCurly) {
                            self.expect(Kind::Comma);
                        }
                    }
                }

                self.expect(Kind::RCurly);
                let obj_expr = Expression::ObjectExpression(
                    self.ast.alloc_object_expression(self.end_span(obj_span), properties),
                );
                // Check for type assertion after object expression
                self.parse_type_assertion_if_present(obj_expr)
            } else {
                // Not a leading-dot expression, parse as normal object expression
                // We've already consumed the opening brace, so we need to parse the rest
                let (object_expression_properties, comma_span) =
                    self.context_add(Context::In, |p| {
                        p.parse_delimited_list(
                            Kind::RCurly,
                            Kind::Comma,
                            opening_span,
                            Self::parse_object_expression_property,
                        )
                    });
                if let Some(comma_span) = comma_span {
                    self.state.trailing_commas.insert(obj_span, self.end_span(comma_span));
                }
                self.expect(Kind::RCurly);
                let obj_expr = Expression::ObjectExpression(self.ast.alloc_object_expression(
                    self.end_span(obj_span),
                    object_expression_properties,
                ));
                // Check for type assertion after object expression
                self.parse_type_assertion_if_present(obj_expr)
            }
        } else {
            self.parse_assignment_expression_or_higher()
        };

        self.ast.alloc_object_property(
            self.end_span(span),
            PropertyKind::Init,
            key,
            value,
            /* method */ false,
            /* shorthand */ false,
            /* computed */ computed,
        )
    }

    /// `PropertyName`[Yield, Await] :
    ///    `LiteralPropertyName`
    ///    `ComputedPropertyName`[?Yield, ?Await]
    pub(crate) fn parse_property_name(&mut self) -> (PropertyKey<'a>, bool) {
        let mut computed = false;
        let key = match self.cur_kind() {
            Kind::Str => PropertyKey::from(self.parse_literal_expression()),
            kind if kind.is_number() => PropertyKey::from(self.parse_literal_expression()),
            // { [foo]() {} }
            Kind::LBrack => {
                computed = true;
                PropertyKey::from(self.parse_computed_property_name())
            }
            _ => {
                let ident = self.parse_identifier_name();
                PropertyKey::StaticIdentifier(self.alloc(ident))
            }
        };
        (key, computed)
    }

    /// `ComputedPropertyName`[Yield, Await] : [ `AssignmentExpression`[+In, ?Yield, ?Await] ]
    pub(crate) fn parse_computed_property_name(&mut self) -> Expression<'a> {
        self.bump_any(); // advance `[`

        let expression = self.context_add(Context::In, Self::parse_assignment_expression_or_higher);

        self.expect(Kind::RBrack);
        expression
    }

    /// Parse type assertion (as or satisfies) if present after an expression
    /// Returns the expression wrapped in type assertion if found, otherwise returns the original expression
    fn parse_type_assertion_if_present(&mut self, expr: Expression<'a>) -> Expression<'a> {
        let kind = self.cur_kind();
        if matches!(kind, Kind::As | Kind::Satisfies) {
            if !self.cur_token().is_on_new_line() {
                let lhs_span = self.start_span();
                self.bump_any();
                let type_annotation = self.parse_ts_type();
                let span = self.end_span(lhs_span);
                if kind == Kind::As {
                    if !self.is_ts {
                        self.error(diagnostics::as_in_ts(span));
                    }
                    self.ast.expression_ts_as(span, expr, type_annotation)
                } else {
                    if !self.is_ts {
                        self.error(diagnostics::satisfies_in_ts(span));
                    }
                    self.ast.expression_ts_satisfies(span, expr, type_annotation)
                }
            } else {
                expr
            }
        } else {
            expr
        }
    }

    /// `MethodDefinition`[Yield, Await] :
    ///   get `ClassElementName`[?Yield, ?Await] ( ) { `FunctionBody`[~Yield, ~Await] }
    ///   set `ClassElementName`[?Yield, ?Await] ( `PropertySetParameterList` ) { `FunctionBody`[~Yield, ~Await] }
    fn parse_method_getter_setter(
        &mut self,
        span: u32,
        kind: PropertyKind,
        modifiers: &Modifiers<'a>,
    ) -> Box<'a, ObjectProperty<'a>> {
        let (key, computed) = self.parse_property_name();
        let function = self.parse_method(false, false, FunctionKind::ObjectMethod);
        match kind {
            PropertyKind::Get => self.check_getter(&function),
            PropertyKind::Set => self.check_setter(&function),
            PropertyKind::Init => {}
        }
        self.verify_modifiers(
            modifiers,
            ModifierFlags::empty(),
            true,
            diagnostics::modifier_cannot_be_used_here,
        );
        self.ast.alloc_object_property(
            self.end_span(span),
            kind,
            key,
            Expression::FunctionExpression(function),
            /* method */ false,
            /* shorthand */ false,
            /* computed */ computed,
        )
    }
}
