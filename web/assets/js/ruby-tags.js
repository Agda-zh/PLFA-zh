// remove extra spaces
const newline = /(?<=[，。、：；」）])\n(?!\n)/gu;
const space = /\s*(<.+?>\p{Script=Han}.*?<\/.+?>)\s*/gu;
const paras = document.querySelectorAll("article > div > p");
for (const p of paras) {
  p.innerHTML = p.innerHTML.replace(newline, "");
  p.innerHTML = p.innerHTML.replace(space, "$1");
}

// set ruby style
const strongs = document.querySelectorAll("strong");
const regex = /(\p{Script=Han}.*?)（(.+?)）/u;
for (const term of strongs) {
  const text = term.innerText.match(regex);
  if (text != null) {
    const zh = text[1];
    const en = text[2];
    term.innerHTML = `
<div class="term">
  <div class="term-zh">${zh}</div>
  <div class="term-en">${en}</div>
</div>`;
  }
}
const terms = document.getElementsByClassName("term-zh");
for (const term of terms) {
  const len = term.innerText.length;
  console.log(len);
  term.parentElement.style.width = len + "em";
}
