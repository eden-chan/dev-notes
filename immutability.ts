class ImmutableList<T> {
  private readonly _list: ReadonlyArray<T>;
  private _deepCloneItem(item: T) {
    return JSON.parse(JSON.stringify(item)) as T;
  }
  public constructor(initialValue?: Array<T>) {
    this._list = initialValue || [];
  }
  public add(newItem: T) {
    const clone = this._list.map((i) => this._deepCloneItem(i));
    const newList = [...clone, newItem];
    const newInstance = new ImmutableList<T>(newList);
    return newInstance;
  }
  public remove(
    item: T,
    areEqual: (a: T, b: T) => boolean = (a, b) => a === b
  ) {
    const newList = this._list
      .filter((i) => !areEqual(item, i))
      .map((i) => this._deepCloneItem(i));
    const newInstance = new ImmutableList<T>(newList);
    return newInstance;
  }
  public get(index: number): T | undefined {
    const item = this._list[index];
    return item ? this._deepCloneItem(item) : undefined;
  }
  public find(filter: (item: T) => boolean) {
    const item = this._list.find(filter);
    return item ? this._deepCloneItem(item) : undefined;
  }
}

interface Hero {
  name: string;
  powers: string[];
}

const heroes = [
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

const hulk = {
  name: "Hulk",
  powers: [
    "superhuman strength",
    "superhuman speed",
    "superhuman Stamina",
    "superhuman durability",
  ],
};

const l1 = new ImmutableList<Hero>(heroes);
const l2 = l1.add(hulk);
const res1 = l1.find((h) => h.name === "Hulk");
const res2 = l2.find((h) => h.name === "Hulk");

const isEq = l1 === l2;

console.group();
console.log(l1);
console.log(l2);
console.assert(isEq, "list are not equal");
console.table({ l1, l2 });
console.groupEnd();

// Creating our own immutable data structures is, in most cases, not necessary.
// In a real-world application, we can use libraries such as Immutable.js to enjoy immutable data structures.
