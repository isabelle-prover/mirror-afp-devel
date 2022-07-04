/* constants */

const CLASS_OBFUSCATED = 'obfuscated'
const CLASS_LINK = 'link'
const ATTRIBUTE_DATA = 'data'


/* handler */

const deobfuscate_href = (ev) => {
  const elem = ev.target
  if (elem.classList.contains(CLASS_OBFUSCATED)) {
    const data = elem.getAttribute(ATTRIBUTE_DATA)
    const email = JSON.parse(atob(data))
    const href = "mailto:" + email.user.join('.') + '@' + email.host.join('.')
    elem.setAttribute("href", href)
    elem.classList.remove(CLASS_OBFUSCATED)
  }
}


/* init */

function init_obfuscated() {
  for (const elem of document.getElementsByClassName(CLASS_OBFUSCATED)) {
    elem.classList.add(CLASS_LINK)
    elem.addEventListener('mouseenter', deobfuscate_href)
    elem.addEventListener('click', deobfuscate_href)
  }
}

document.addEventListener('DOMContentLoaded', init_obfuscated)
