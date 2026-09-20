declare const process: { stdout: { write(text: string): void } };

interface Box {
    items: number[];
    bias: number;
    method(value: number): number;
}

function probe(box: Box | null): void {
    let calls = 0;
    function key(): number {
        calls++;
        return 0;
    }
    const factory: (() => Box) | null = box === null ? null : () => box;
    const indexed = box?.items[key()];
    const invoked = box?.method(key());
    const generated = factory?.().items[key()];
    const asserted = box?.items![key()];
    const groupedMethod = (box?.method)?.(key());
    const deleted = delete box?.items[key()];
    process.stdout.write(JSON.stringify([
        indexed ?? -1,
        invoked ?? -1,
        generated ?? -1,
        asserted ?? -1,
        groupedMethod ?? -1,
        deleted,
        calls,
    ]) + "\n");
}

probe(null);
probe({ items: [7], bias: 40, method(value: number): number { return this.bias + value; } });
