// Pins declaration-owned self-captures and lexical TDZ. Resolving a binding
// through the wrong slot (outer instead of the hole, or a cloned function
// identity) changes the lines. Interpreter/JIT/AOT must match Node 24.

export {};

function runSelfCaptures(): void {
  const arrow = () => arrow;
  function recursive() {
    return recursive;
  }
  class Self {
    method() {
      return Self;
    }
  }
  const { destructured = () => destructured } = {};
  const shadowed = () => shadowed;
  {
    const shadowed = 0;
    void shadowed;
  }
  process.stdout.write(`${arrow() === arrow}\n`);
  process.stdout.write(`${recursive() === recursive}\n`);
  process.stdout.write(`${new Self().method() === Self}\n`);
  process.stdout.write(`${destructured() === destructured}\n`);
  process.stdout.write(`${shadowed() === shadowed}\n`);
}
runSelfCaptures();

function outcome(operation: () => unknown): string {
  try {
    return String(operation());
  } catch (error) {
    return (error as { name: string }).name;
  }
}
function earlyRead(): string {
  const read = () => later;
  const observed = outcome(read);
  let later = 1;
  void later;
  return observed;
}
function lateRead(): number {
  const read = () => later;
  let later = 1;
  return read();
}
function hoisted(): number {
  return declaredLater();
  function declaredLater() {
    return 2;
  }
}
function blockRead(): string {
  let value = 1;
  void value;
  {
    const read = () => value;
    const observed = outcome(read);
    let value = 2;
    void value;
    return observed;
  }
}
function localClassName(): boolean {
  class LocalClass {
    static value = LocalClass;
  }
  return LocalClass.value === LocalClass;
}
const heritage = outcome(() => {
  class C extends C {}
  return C;
});
const expressionHeritage = outcome(() => class C extends C {});
class StaticClass {
  static value = StaticClass;
}
const staticClassName = String(StaticClass.value === StaticClass);
const typeResult = outcome(() => {
  // @ts-expect-error Even typeof must throw inside a lexical binding's TDZ.
  return typeof value;
  let value;
});
process.stdout.write(
  [
    earlyRead(),
    lateRead(),
    hoisted(),
    heritage,
    expressionHeritage,
    staticClassName,
    String(localClassName()),
    blockRead(),
    typeResult,
  ].join("\n") + "\n",
);
