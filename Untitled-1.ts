// Most FP languages feature lazy-evaluated APIs.
// Lazy evaluation is when operations are not computed until they have to have to be.
// Basically they procrastinate until the last moment right before the deadline, similar to what I do for my Crowdmark assignments.

// This function finds an element in an array, but when it is invoked,
// we don't filter tnhe array. Instead we declare a proxy and a handler.
function lazyFind<T>(arr: T[], filter: (i: T) => boolean): T {
  let hero: T | null = null;

  const proxy = new Proxy(
    {},
    {
      get: (obj, prop) => {
        console.log("Filtering...");
        if (!hero) {
          hero = arr.find(filter) || null;
        }
        return hero ? (hero as any)[prop] : null;
      },
    }
  );

  return proxy as any;
}

// It's only later, when one of the properties in the
// result is accessed, that the proxy handler is invoked and filtering takes place.

const ___heroes = [
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

console.log("A");
const __spiderman = lazyFind(___heroes, (h) => h.name === "Spiderman");
console.log("B");
console.log(__spiderman.name);
console.log("C");

/*
    A
    B
    Filtering...
    Spiderman
    C
*/
