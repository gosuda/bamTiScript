const SIZE: number = 4 * 1024 * 1024;
let state: number = 0x24596b5d | 0;
const chunks: string[] = [];
let built: number = 0;
while (built < SIZE) {
  state = (Math.imul(state, 1103515245) + 12345) | 0;
  const pick: number = (state >>> 16) % 10;
  if (pick < 3) {
    state = (Math.imul(state, 1103515245) + 12345) | 0;
    const nameLen: number = 4 + ((state >>> 16) % 5);
    let name: string = "";
    for (let i: number = 0; i < nameLen; i++) {
      state = (Math.imul(state, 1103515245) + 12345) | 0;
      name += String.fromCharCode(97 + ((state >>> 16) % 26));
    }
    state = (Math.imul(state, 1103515245) + 12345) | 0;
    const hostLen: number = 4 + ((state >>> 16) % 5);
    let host: string = "";
    for (let i: number = 0; i < hostLen; i++) {
      state = (Math.imul(state, 1103515245) + 12345) | 0;
      host += String.fromCharCode(97 + ((state >>> 16) % 26));
    }
    const token: string = name + "@" + host + ".com ";
    chunks.push(token);
    built += token.length;
  } else {
    state = (Math.imul(state, 1103515245) + 12345) | 0;
    const wordLen: number = 3 + ((state >>> 16) % 6);
    let word: string = "";
    for (let i: number = 0; i < wordLen; i++) {
      state = (Math.imul(state, 1103515245) + 12345) | 0;
      word += String.fromCharCode(97 + ((state >>> 16) % 26));
    }
    const token: string = word + " ";
    chunks.push(token);
    built += token.length;
  }
}
const text: string = chunks.join("").slice(0, SIZE);
const re: RegExp = /(\w+)@(\w+)\.com/g;
let found: RegExpExecArray | null;
let checksum: number = 0;
while ((found = re.exec(text)) !== null) {
  checksum += found[1].length * 1009 + found[2].length * 1013 + 7;
}
console.log(Math.floor(checksum));
