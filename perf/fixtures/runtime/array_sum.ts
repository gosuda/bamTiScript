function sum(a: number[]): number {
  let total: number = 0;
  for (let i: number = 0; i < a.length; i++) {
    total += a[i];
  }
  return total;
}
const size: number = 10000;
const calls: number = 10000;
const intArr: number[] = new Array(size);
for (let i: number = 0; i < size; i++) {
  intArr[i] = i;
}
const fracArr: number[] = new Array(size);
for (let i: number = 0; i < size; i++) {
  fracArr[i] = i + 0.5;
}
let checksum: number = 0;
for (let k: number = 0; k < calls; k++) {
  checksum += sum(intArr);
}
for (let k: number = 0; k < calls; k++) {
  checksum += sum(fracArr);
}
console.log(Math.floor(checksum));
