type Quad = { aa: number; bb: number; cc: number; dd: number };
let seed: number = 88675123 | 0;
function nextInt(): number {
  seed = seed ^ ((seed << 13) | 0);
  seed = seed ^ (seed >>> 17);
  seed = seed ^ ((seed << 5) | 0);
  return seed | 0;
}
function sumQuad(item: Quad): number {
  return item.aa + item.bb + item.cc + item.dd;
}
let count: number = 1000000;
let items: Quad[] = [];
for (let i: number = 0; i < count; i++) {
  let v0: number = nextInt();
  let v1: number = nextInt();
  let v2: number = nextInt();
  let v3: number = nextInt();
  let shape: number = i & 3;
  let obj: Quad;
  if (shape === 0) {
    obj = { aa: v0, bb: v1, cc: v2, dd: v3 };
  } else if (shape === 1) {
    obj = { bb: v1, cc: v2, dd: v3, aa: v0 };
  } else if (shape === 2) {
    obj = { cc: v2, dd: v3, aa: v0, bb: v1 };
  } else {
    obj = { dd: v3, aa: v0, bb: v1, cc: v2 };
  }
  items.push(obj);
}
let checksum: number = 0;
for (let i: number = 0; i < count; i++) {
  checksum = (checksum + sumQuad(items[i])) | 0;
}
console.log(checksum);
