class Point8 {
  a: number;
  b: number;
  c: number;
  d: number;
  e: number;
  f: number;
  g: number;
  h: number;
  constructor(a: number, b: number, c: number, d: number, e: number, f: number, g: number, h: number) {
    this.a = a;
    this.b = b;
    this.c = c;
    this.d = d;
    this.e = e;
    this.f = f;
    this.g = g;
    this.h = h;
  }
}
let seed: number = 362437 | 0;
function nextInt(): number {
  seed = seed ^ ((seed << 13) | 0);
  seed = seed ^ (seed >>> 17);
  seed = seed ^ ((seed << 5) | 0);
  return seed | 0;
}
let poolSize: number = 16;
let pool: Point8[] = [];
for (let i: number = 0; i < poolSize; i++) {
  pool.push(new Point8(nextInt(), nextInt(), nextInt(), nextInt(), nextInt(), nextInt(), nextInt(), nextInt()));
}
let iterations: number = 10000000;
let checksum: number = 0;
for (let i: number = 0; i < iterations; i++) {
  let item: Point8 = pool[i & 15];
  checksum = (checksum + item.a + item.b + item.c + item.d + item.e + item.f + item.g + item.h) | 0;
}
console.log(checksum);
