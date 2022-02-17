//  A function is a first-class citizen if it can do everything that a variable can do
const _heroes = [
  {
    name: "Spiderman",
    powers: [
      "wall-crawling",
      "enhanced strength",
      "enhanced speed",
      "spider-Sense",
    ],
  },
  {
    name: "Superman",
    powers: ["flight", "superhuman strength", "x-ray vision", "super-speed"],
  },
];

//  find takes a function as its second arg
function find<T>(arr: T[], filter: (i: T) => boolean) {
  return arr.filter(filter);
}

find(_heroes, (h) => h.name === "Spiderman");

//  Or it can be returned by another function. For example, the following
//  function takes a function as its only argument and returns a function
function _find<T>(filter: (i: T) => boolean) {
  return (arr: T[]) => arr.filter(filter);
}

//  Functions can also be assigned to variables.
const findSpiderman = _find((h: Hero) => h.name === "Spiderman");
const spiderman = findSpiderman(_heroes);

console.log(spiderman);

// Lambda expressions are just expressions that can be used to declare
// anonymous functions ( functions without a name )
// Before ES6 specification, the only way to assign a function as a value to a variable was to use a function expression
const log = function (arg: any) {
  console.log(arg);
};

// With ES6, we can now assign a function as a value to variable using arrow function syntax
const _log = (arg: any) => console.log(arg);
_log("what does the future look like, and why is it crypto?");

// The arity of a function is the number of arguments the function takes
// a unary function is a function that takes only one argument
// Unary functions are very important in functional programming because
// they facilitate utilization of the function composition pattern.

const isNull =
  <T>(a: T | null) =>
  (boolean) =>
    a === null;

// A binary function is a function that takes two arguments.
const add = (a: number, b: number) => (number) => a + b;

// A ternary function is a function that takes three arguments
// A variadic function is a function that accepts a variable number of arguments
// Functions with two or more arguments are also important because some of the most
//  common FP patterns and techniques (for example, partial application and currying)
// have been designed to transform functions that allow multiple arguments into unary functions.
const addMany = (...numbers: number[]) =>
  numbers.reduce((acc, cur) => acc + cur, 0);

console.log(addMany(1, 2, 3, 4, 5)); // prints 15

// A higher-order fnuction is a function that does at least one of the following:
//  takes one or more functions as arguments
//   returns a function as its result

function addDelay(msg: string, ms: number) {
  return () => {
    setTimeout(() => {
      console.log(msg);
    }, ms);
  };
}

const delayedSayHello = addDelay("Hello world!", 1000);
delayedSayHello(); // Prints "Hello world!" (after 1000 ms)

// We can do better with currying.
const _addDelay = (func: () => void, ms: number) => () =>
  setTimeout(() => {
    func();
  }, ms);

const _sayHello = () => {
  console.log("Curried hello world");
};
const _delayedSayHello = _addDelay(_sayHello, 1000);
_delayedSayHello(); // prints "Curried hello world" after 1000ms
