//! ArkUI AST node definitions
//!
//! This module contains AST node definitions for HarmonyOS ArkUI syntax including:
//! - Struct declarations (`struct ComponentName { ... }`)
//! - ArkUI component expressions (`Column() { ... }`)
//!
//! ArkUI is a declarative UI framework for HarmonyOS applications.

use oxc_allocator::{Box, CloneIn, Dummy, GetAddress, TakeIn, UnstableAddress, Vec};
use oxc_ast_macros::ast;
use oxc_estree::ESTree;
use oxc_span::{ContentEq, GetSpan, GetSpanMut, Span};
use oxc_syntax::scope::ScopeId;
use std::cell::Cell;

use super::{js::*, ts::*};

/// Struct Declaration Statement
///
/// Represents an ArkUI struct declaration, which is similar to a class but uses the `struct` keyword.
///
/// ## Example
/// ```arkui
/// @ComponentV2
/// struct MyComponent {
///   @Local message: string = 'Hello World';
///   build() {
///     Column() {
///       Text(`Parent message: ${this.message}`)
///     }
///   }
/// }
/// ```
#[ast(visit)]
#[scope(flags = ScopeFlags::StrictMode)]
#[derive(Debug)]
#[generate_derive(CloneIn, Dummy, TakeIn, GetSpan, GetSpanMut, ContentEq, ESTree, UnstableAddress)]
pub struct StructStatement<'a> {
    /// Span
    pub span: Span,
    /// Decorators applied to the struct.
    ///
    /// Common decorators include `@ComponentV2`, `@Entry`, etc.
    ///
    /// ## Example
    /// ```arkui
    /// @ComponentV2  // <- decorator
    /// @Entry        // <- decorator
    /// struct MyComponent {}
    /// ```
    pub decorators: Vec<'a, Decorator<'a>>,
    /// Struct identifier, AKA the name
    pub id: BindingIdentifier<'a>,
    /// Type parameters (for generic structs, if supported)
    #[ts]
    pub type_parameters: Option<Box<'a, TSTypeParameterDeclaration<'a>>>,
    /// Struct body containing properties and methods
    pub body: Box<'a, StructBody<'a>>,
    /// Id of the scope created by the [`StructStatement`], including type parameters and
    /// statements within the [`StructBody`].
    pub scope_id: Cell<Option<ScopeId>>,
}

/// Struct Body
///
/// Contains the elements (properties and methods) within a struct declaration.
#[ast(visit)]
#[derive(Debug)]
#[generate_derive(CloneIn, Dummy, TakeIn, GetSpan, GetSpanMut, ContentEq, ESTree, UnstableAddress)]
pub struct StructBody<'a> {
    /// Span
    pub span: Span,
    /// Elements within the struct body
    pub body: Vec<'a, StructElement<'a>>,
}

/// Struct Body Element
///
/// Represents an element within a struct body, which can be:
/// - Property definitions (with decorators like `@Param`, `@Local`, `@Once`)
/// - Method definitions (like `build()`)
///
/// ## Example
/// ```arkui
/// struct MyComponent {
///   @Param @Once onceParam: string = '';  // StructElement::PropertyDefinition
///   @Local message: string = 'Hello';      // StructElement::PropertyDefinition
///   build() {                              // StructElement::MethodDefinition
///     Column() {}
///   }
/// }
/// ```
#[ast(visit)]
#[builder(skip)]
#[derive(Debug)]
#[generate_derive(CloneIn, Dummy, TakeIn, GetSpan, GetSpanMut, GetAddress, ContentEq, ESTree)]
pub enum StructElement<'a> {
    /// Property definitions with decorators
    ///
    /// Properties can have decorators like `@Param`, `@Local`, `@Once`, etc.
    PropertyDefinition(Box<'a, PropertyDefinition<'a>>) = 0,
    /// Method definitions (like `build()`)
    MethodDefinition(Box<'a, MethodDefinition<'a>>) = 1,
}

/// ArkUI Component Expression
///
/// Represents an ArkUI component call expression with children, similar to JSX but using
/// function call syntax.
///
/// ## Example
/// ```arkui
/// Column() {
///   Text(`onceParam: ${this.onceParam}`)
///   Button('change message')
///     .onClick(() => {
///       this.message = 'Hello Tomorrow';
///     })
/// }
/// ```
///
/// This is similar to JSX but uses function call syntax:
/// - JSX: `<Column><Text>Hello</Text></Column>`
/// - ArkUI: `Column() { Text('Hello') }`
#[ast(visit)]
#[derive(Debug)]
#[generate_derive(CloneIn, Dummy, TakeIn, GetSpan, GetSpanMut, ContentEq, ESTree, UnstableAddress)]
pub struct ArkUIComponentExpression<'a> {
    /// Span
    pub span: Span,
    /// The component name/callee (e.g., `Column`, `Text`, `Button`)
    pub callee: Expression<'a>,
    /// Type arguments for generic components (if supported)
    #[ts]
    pub type_arguments: Option<Box<'a, TSTypeParameterInstantiation<'a>>>,
    /// Arguments passed to the component constructor
    ///
    /// ## Example
    /// ```arkui
    /// Button('change message')  // <- arguments contains StringLiteral('change message')
    /// ```
    pub arguments: Vec<'a, Argument<'a>>,
    /// Children of the component (the content inside `{ ... }`)
    ///
    /// Children can be:
    /// - Other ArkUI component expressions
    /// - Text expressions
    /// - Template literals
    /// - Regular expressions
    pub children: Vec<'a, ArkUIChild<'a>>,
    /// Chain expressions (like `.onClick(...)`)
    ///
    /// ArkUI supports method chaining on components:
    /// ```arkui
    /// Button('click me')
    ///   .onClick(() => { ... })  // <- chain_expression (CallExpression with MemberExpression callee)
    /// ```
    ///
    /// Each chain expression is a `CallExpression` where the callee is a `MemberExpression`.
    /// The chain is built by nesting these expressions.
    pub chain_expressions: Vec<'a, CallExpression<'a>>,
}

/// ArkUI Child
///
/// Represents a child element within an ArkUI component expression.
///
/// ## Example
/// ```arkui
/// Column() {
///   Text('Hello')                    // ArkUIChild::Component
///   Button('Click')                  // ArkUIChild::Component
///   `Template: ${value}`             // ArkUIChild::Expression
///   if (condition) {                  // ArkUIChild::Statement
///     Text('Conditional')
///   }
/// }
/// ```
#[ast(visit)]
#[builder(skip)]
#[derive(Debug)]
#[generate_derive(CloneIn, Dummy, TakeIn, GetSpan, GetSpanMut, GetAddress, ContentEq, ESTree)]
pub enum ArkUIChild<'a> {
    /// Another ArkUI component expression (nested component)
    Component(Box<'a, ArkUIComponentExpression<'a>>) = 0,
    /// A regular expression (for text, template literals, etc.)
    Expression(Box<'a, Expression<'a>>) = 1,
    /// A statement (for control flow like if, for, etc.)
    Statement(Box<'a, Statement<'a>>) = 2,
}
