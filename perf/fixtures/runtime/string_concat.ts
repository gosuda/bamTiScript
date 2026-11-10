let state: number = 0x1f2b3c4d | 0;
function nextUnit(): number {
  state = (Math.imul(state, 1103515245) + 12345) | 0;
  return 97 + ((state >>> 16) % 26);
}
const appends: number = 62500;
let text: string = "";
for (let n: number = 0; n < appends; n++) {
  const piece: string = String.fromCharCode(
    nextUnit(), nextUnit(), nextUnit(), nextUnit(),
    nextUnit(), nextUnit(), nextUnit(), nextUnit(),
    nextUnit(), nextUnit(), nextUnit(), nextUnit(),
    nextUnit(), nextUnit(), nextUnit(), nextUnit()
  );
  text += piece;
}
console.log(text.length + " " + text.charCodeAt(text.length - 1));
