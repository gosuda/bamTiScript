type Pair = { x: number; y: number };
let seed: number = 41018436 | 0;
function nextInt(): number {
  seed = seed ^ ((seed << 13) | 0);
  seed = seed ^ (seed >>> 17);
  seed = seed ^ ((seed << 5) | 0);
  return seed | 0;
}
let iterations: number = 10000000;
let survivors: Pair[] = [];
let checksum: number = 0;
for (let i: number = 0; i < iterations; i++) {
  let cell: Pair = { x: nextInt(), y: nextInt() };
  checksum = (checksum + cell.x) | 0;
  if (i % 1000 === 0) {
    survivors.push(cell);
  }
}
let survivorFold: number = 0;
for (let i: number = 0; i < survivors.length; i++) {
  survivorFold = (survivorFold + survivors[i].y) | 0;
}
checksum = (checksum + survivors.length + survivorFold) | 0;
console.log(checksum);
