declare const process: { stdout: { write(text: string): void } };

interface Row { readonly id: number; readonly score: number; }
const rows: readonly Row[] = [{ id: 1, score: 5 }, { id: 2, score: 9 }, { id: 3, score: 3 }];
const total = rows.filter(row => row.score > 3).reduce((sum, row) => sum + row.score, 0);
process.stdout.write(String(total) + "\n");

const callbacks: (() => number)[] = [];
for (let i = 0; i < 5; i++) { callbacks.push(() => i); }
process.stdout.write(callbacks.map(callback => callback()).join(",") + "\n");

let a = 1;
let b = 2;
[a, b] = [b, a];
let defaults = 0;
function nextDefault(): number { defaults++; return defaults; }
const { x = nextDefault(), y = nextDefault() } = { x: 7, y: undefined };
process.stdout.write([a, b, x, y, defaults].join(",") + "\n");

const counts = new Map<number, number>();
for (const value of [3, 1, 4, 1, 5]) { counts.set(value, (counts.get(value) ?? 0) + 1); }
const sorted = Array.from(counts.keys()).sort((left, right) => left - right);
process.stdout.write(sorted.map(key => key + ":" + counts.get(key)).join(",") + "\n");

function* squares(limit: number): Generator<number> {
    for (let i = 0; i < limit; i++) { yield i * i; }
}
let sum = 0;
for (const value of squares(8)) { sum += value; }
process.stdout.write(String(sum) + "\n");

function cleanup(limit: number): number {
    let result = 0;
    outer: for (let i = 0; i < limit; i++) {
        try {
            if (i % 3 === 0) { continue outer; }
            if (i === 7) { break outer; }
            result += i;
        } finally { result += 10; }
    }
    return result;
}
process.stdout.write(String(cleanup(20)) + "\n");

async function increment(value: number): Promise<number> {
    return (await Promise.resolve(value)) + 1;
}
increment(41).then(value => process.stdout.write(String(value) + "\n"));
