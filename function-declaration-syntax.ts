//  Lots of nuance in function declaration syntax

// variable hoisting
// JS interpreter can evaluate a function declaration as it is being parsed
// But the function expression is part of an assaginment and will not be
// evaluated until the assignment has been completed

console.log(greetNamed("John")); // OK
// console.log(greetUnnamed("John")); // Error

function greetNamed(name: string): string {
  return "Hi! ${name}";
}

let greetUnnamed = function (name: string): string {
  return "Hi! ${name}";
};

// Trailing commas in function arguments just in case we forget comma
// 🙏🏼 VSCode for checking for you!

// optional parameters (var?)
// default parameters  (var=0)
// must always be located after any required parameters in the function's parameter list.

function add_ts(foo: number, bar: number, foobar: number = 0): number {
  return foo + bar + foobar;
}

// TS compiles down to JS
function add_js(foo, bar, foobar) {
  if (foobar === void 0) {
    // void 0 is used by TS compiler to check whether a variable is  equal to undefined.
    // you can actually modify the "undefined" variable, like var undefined = 2
    // THUS void 0 will always evaluate as undefined, making it more secure.
    foobar = 0;
  }
  return foo + bar + foobar;
}

// rest parameters (...var)
// describe functions with an unknown number of arguments
// JS functions have built-in object called the arguments object
// arguments is a local variable, and contains objects such as an array,
// which includes the arguments used when the function was invoked
// https://developer.mozilla.org/en-US/docs/Web/JavaScript/Reference/Functions/arguments

// Overload signatures
// In Typescript, we can overload a function by specifying all function signatures aka overload signatures,followed by
// a signature aka implementation signature.

function test(name: string): string; // overloaded signature
function test(age: number): string; // overloaded signature
function test(single: boolean): string; // overloaded signature
function test(value: string | number | boolean): string {
  // implementation signature
  switch (typeof value) {
    case "string":
      return `My name is ${value}.`;
    case "number":
      return `I'm ${value} years old.`;
    case "boolean":
      return value ? "I'm single." : "I'm not single.";
    default:
      throw new Error("Invalid Operation!");
  }
}

// The implementation signature must be compatible with all the overloaded signatures,
// always be the last in the list, and take any or a union type as the type of its parameters.

// We can use a specialized signature to create multiple methods with the same name and number of parameters, but a different return type.
// To create a specialized signature, we must indicate the type of function parameter using a string.
//  The string literal is used to identify which of the function overloads is invoked:
// When we declare a specialized signature in an object, it must be assignable to at least one non-specialized signature in the same object.
interface Document {
  createElement(tagName: "div"): HTMLDivElement; // specialized
  createElement(tagName: "span"): HTMLSpanElement; // specialized
  createElement(tagName: "canvas"): HTMLCanvasElement; // specialized
  createElement(tagName: string): HTMLElement; // non-specialized
}

// lexical scoping - structure of program source code determines what variables are referred to
// dynamic scoping - runtime state of the program stack to determine what variable is referred to
// TS uses lexical scoping, and is much easier to understand

// const foo = (): void => {
//   if (true) {
//     var theTruthAboutPD: string = "pd is great";
//     if (true) {
//       var isEdenCool: boolean = true;
//     }
//   }
//   console.log(theTruthAboutPD, isEdenCool); // pd is great, true
// };

// You'd think the preceding code sample would throw an error
// since the bar variable should be out of scope when the log function is invoked.
// However, if we invoke the foo function, the log function will be able to display
// the variable bar without errors because all variables inside a function will be within
// the scope of the entire function body, even if they are inside another block of code (except a function block).

// So the lexical scope is everything inside foo.
// foo(); // pd is really great, true

// HOISTING
// at runtime, all the variable declarations are moved to the top of a function before the function is executed.
// This behavior is known as hoisting, and is specific to javascript runtime.
// function _foo(): void {
//   bar = 0;
//   var bar: number;
//   console.log(bar);
// }
// is compiled to
// function foo() {
//   var bar;
//   if (true) {
//     bar = 0;
//   }
//   console.log(bar);
// }
// foo(); // 0

// block scoping
// let sets the scope of a variable to a block (if, while, for, {...})

// const __foo(): void {
//   if (true) {
//     let bar:number=0;
//     bar=1;
//   }
//   // console.log(bar); ERROR
// }
// __foo()

// An immediately-invoked function expression (IIFE) is a design pattern that produces a lexical scope using function scoping.
//  IIFE can be used to avoid variable hoisting from within blocks or to prevent us from polluting the global scope, for example:

let bar = 0; // global

(function () {
  let foo: number = 0; // In scope of this function
  bar = 1; // Access global scope
  console.log(bar); // 1
  console.log(foo); // 0
})();

console.log(bar); // 1
// console.log(foo); // Error
