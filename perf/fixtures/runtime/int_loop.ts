function mix(seed: number): number {
  let s: number = seed | 0;
  for (let i: number = 0; i < 10000; i++) {
    s = (s + i) | 0;
    s = Math.imul(s, 1103515245);
    s = (s ^ (s >>> 13)) | 0;
  }
  return s | 0;
}
let seed: number = 0x12345678 | 0;
let checksum: number = 0;
for (let k: number = 0; k < 10000; k++) {
  seed = mix(seed);
  checksum = (checksum + seed) | 0;
}
console.log(checksum);
