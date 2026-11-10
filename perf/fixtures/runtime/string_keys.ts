let keyCount: number = 64;
let readCount: number = 1000000;
let keys: string[] = [];
for (let i: number = 0; i < keyCount; i++) {
  keys.push("field" + "_" + i);
}
let store: { [key: string]: number } = {};
let seed: number = 2463534242 | 0;
function nextInt(): number {
  seed = seed ^ ((seed << 13) | 0);
  seed = seed ^ (seed >>> 17);
  seed = seed ^ ((seed << 5) | 0);
  return seed | 0;
}
for (let i: number = 0; i < keyCount; i++) {
  store[keys[i]] = nextInt();
}
let checksum: number = 0;
for (let i: number = 0; i < readCount; i++) {
  checksum = (checksum + store[keys[i & 63]]) | 0;
}
console.log(checksum);
