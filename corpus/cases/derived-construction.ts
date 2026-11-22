// Pins derived-class construction: super control-flow, return overrides,
// default constructors, field init after abrupt bases, and new.target identity.
// A wrong super-before-this, return-override, or most-derived new.target
// changes labeled stdout. Interpreter/JIT/AOT must match Node 24.

export {};

class Base {
  value: unknown;
  constructor(value: unknown) {
    this.value = value;
  }
}

function capture(label: string, construct: () => { value: unknown }): void {
  try {
    const value = construct();
    process.stdout.write(`${label}:value=${String(value.value)}\n`);
  } catch (error) {
    process.stdout.write(
      `${label}:ReferenceError=${error instanceof ReferenceError}\n`,
    );
  }
}

capture("super.conditional-true", () => new class extends Base {
  constructor() {
    if (true) super(1);
  }
}());
capture("super.conditional-false", () => new class extends Base {
  constructor() {
    if (false) super(2);
  }
}());
capture("super.conditional-branches", () => new class extends Base {
  constructor(flag: boolean) {
    if (flag) super(3); else super(4);
  }
}(false));
capture("super.repeated", () => new class extends Base {
  constructor() {
    super(5);
    super(6);
  }
}());
capture("super.looped", () => new class extends Base {
  constructor() {
    while (true) {
      super(7);
    }
  }
}());
capture("super.nested-control", () => new class extends Base {
  constructor() {
    for (const value of [8]) {
      if (value === 8) {
        super(value);
      }
    }
  }
}());

let retryCount = 0;
class RetryBase {
  value: unknown;
  constructor(value: unknown) {
    if (retryCount++ === 0) {
      throw new Error("x");
    }
    this.value = value;
  }
}
capture("super.retry", () => new class extends RetryBase {
  constructor() {
    try {
      super(1);
    } catch {
    }
    super(2);
  }
}());
capture("super.early-object", () => new class extends Base {
  // @ts-expect-error Returning an object before super is valid at runtime.
  constructor() {
    return { value: "early" };
  }
}());
capture("super.state-u-undefined", () => new class extends Base {
  // @ts-expect-error The missing super call must cause a runtime ReferenceError.
  constructor() {}
}());

class ReturnBase {}
function captureReturn(label: string, construct: () => { kind?: string } | ((...args: never[]) => unknown)): void {
  try {
    const value = construct();
    const result = typeof value === "function" ? "function" : value.kind;
    process.stdout.write(`${label}:${result}\n`);
  } catch (error) {
    process.stdout.write(`${label}:TypeError=${error instanceof TypeError}\n`);
  }
}
captureReturn("return.object", () => new class extends ReturnBase {
  constructor() {
    super();
    return { kind: "object" };
  }
}());
captureReturn("return.function", () => new class extends ReturnBase {
  constructor() {
    super();
    return function replacement() {};
  }
}());
captureReturn("return.undefined", () => new class extends ReturnBase {
  kind: string;
  constructor() {
    super();
    this.kind = "initialized-this";
    return undefined;
  }
}());
captureReturn("return.null", () => new class extends ReturnBase {
  constructor() {
    super();
    return null;
  }
}());
captureReturn("return.number", () => new class extends ReturnBase {
  constructor() {
    super();
    return 1;
  }
}());
captureReturn("return.string", () => new class extends ReturnBase {
  constructor() {
    super();
    return "primitive";
  }
}());
captureReturn("return.bare", () => new class extends ReturnBase {
  kind: string;
  constructor() {
    super();
    this.kind = "bare-this";
    return;
  }
}());
captureReturn("return.finally", () => new class extends ReturnBase {
  constructor() {
    super();
    try {
      return 1;
    } finally {
      return { kind: "finally-object" };
    }
  }
}());

class DefaultBase {
  static seenNewTarget: unknown;
  sum: number;
  constructor(first: number, second: number) {
    this.sum = first + second;
    DefaultBase.seenNewTarget = new.target;
  }
}
function captureDefault(
  label: string,
  construct: () => { sum: number; field?: string },
): void {
  try {
    const value = construct();
    const target = DefaultBase.seenNewTarget as { name?: string } | undefined;
    process.stdout.write(
      `${label}:value=${value.sum}:fields=${value.field}:target=${target && target.name}:instanceof=${value instanceof DefaultBase}\n`,
    );
  } catch (error) {
    const err = error as { constructor: { name: string }; message: string };
    process.stdout.write(`${label}:threw=${err.constructor.name}:${err.message}\n`);
  }
}
captureDefault("default.args-target-prototype", () => new (class extends DefaultBase {
  field = "initialized";
})(2, 3));

class PrimitiveReturnBase {
  marker: string;
  constructor() {
    this.marker = "base-this";
    return 42;
  }
}
try {
  const value = new (class extends PrimitiveReturnBase {
    field = "derived-field";
  })();
  process.stdout.write(
    `default.return-override:marker=${value.marker}:field=${(value as { field?: string }).field}:proto=${Object.getPrototypeOf(value).constructor.name}\n`,
  );
} catch (error) {
  process.stdout.write(
    `default.return-override:threw=${(error as { constructor: { name: string } }).constructor.name}\n`,
  );
}

class ThrowingBase {
  constructor() {
    throw new RangeError("abrupt-base");
  }
}
try {
  new (class extends ThrowingBase {
    field = (() => {
      process.stdout.write("default.field-init-after-abrupt\n");
      return 1;
    })();
  })();
  process.stdout.write("default.abrupt:unexpected-success\n");
} catch (error) {
  const err = error as { constructor: { name: string }; message: string };
  process.stdout.write(`default.abrupt:threw=${err.constructor.name}:${err.message}\n`);
}

class ObjectReturnBase {
  marker: string;
  field?: string;
  constructor() {
    this.marker = "base-this";
    return { marker: "replacement", field: "no-fields" };
  }
}
try {
  const value = new (class extends ObjectReturnBase {
    field = "derived-field";
  })();
  process.stdout.write(`default.object-return:marker=${value.marker}:field=${value.field}\n`);
} catch (error) {
  process.stdout.write(
    `default.object-return:threw=${(error as { constructor: { name: string } }).constructor.name}\n`,
  );
}

class TargetBase {
  static seenNewTarget: { name?: string } | undefined;
  sum: number;
  constructor(first: number, second: number) {
    this.sum = first + second;
    TargetBase.seenNewTarget = new.target;
  }
}
class ExplicitMiddle extends TargetBase {
  third: number;
  constructor(first: number, second: number, third: number) {
    super(first, second);
    this.third = third;
  }
}
class ImplicitMiddle extends ExplicitMiddle {}
class Leaf extends ImplicitMiddle {}
function captureTarget(
  label: string,
  construct: () => { sum: number; third: number },
): void {
  try {
    const value = construct();
    const target = TargetBase.seenNewTarget;
    process.stdout.write(
      `${label}:value=${value.sum}:third=${value.third}:target=${target && target.name}:base=${value instanceof TargetBase}:explicit=${value instanceof ExplicitMiddle}:implicit=${value instanceof ImplicitMiddle}:leaf=${value instanceof Leaf}\n`,
    );
  } catch (error) {
    const err = error as { constructor: { name: string }; message: string };
    process.stdout.write(`${label}:threw=${err.constructor.name}:${err.message}\n`);
  }
}
captureTarget("target.leaf-most-derived", () => new Leaf(2, 3, 4));
captureTarget("target.implicit-as-leaf", () => new ImplicitMiddle(5, 6, 7));
captureTarget("target.explicit-as-leaf", () => new ExplicitMiddle(8, 9, 10));
