// Imperative programming is a programming paradigm that uses statements that change a program's state.
// Declarative programming is a programming paradigm that expresses logic without describing its control flow.
// Typescript is not a pure functional programming language, since the complier allows for be side effects
// But we can write TS code with in a functional programming style to minimize side-effects by
// describing what the program does without explicitly stating HOW it does in as a sequence of steps.

// Here are three examples of increasingly declarative code
interface Result {
  id: number;
  result: number;
}

const results: Result[] = [
  { id: 1, result: 64 },
  { id: 2, result: 87 },
  { id: 3, result: 89 },
];

// Imperative
function avg(arr: Result[]) {
  let total = 0;
  for (var i = 0; i < arr.length; i++) {
    total += arr[i].result;
  }
  return total / arr.length;
}

const resultsAvg = avg(results);
console.log(resultsAvg);

// Somewhat declarative
const _add = (a: number, b: number) => a + b;
const _division = (a: number, b: number) => a / b;

const _avg = (arr: Result[]) =>
  _division(arr.map((a) => a.result).reduce(_add, 0), arr.length);

const _resultsAvg = _avg(results);
console.log(_resultsAvg);

// More declarative
const __add = (a: number, b: number) => a + b;
const __addMany = (...args: number[]) => args.reduce(__add, 0);
const __div = (a: number, b: number) => a / b;
const __mapProp = <T>(k: keyof T, arr: T[]) => arr.map((a) => a[k]);
const __avg = (arr: number[]) => __div(addMany(...arr), arr.length);

// This makes me go 🥵
const __resultsAvg = __avg(__mapProp("result", results));
console.log(__resultsAvg);
