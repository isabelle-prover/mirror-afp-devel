/* utilities */

const strip_suffix = (str, suffix) => {
  if (str.endsWith(suffix)) return str.slice(0, -suffix.length)
  else return str
}

const group_by = (elems) => {
  return elems.reduce((ks, kv) => {
    if (kv.isEmpty) return ks
    else {
      const k = kv[0]
      const vs = kv.slice(1)
      if (ks[k]) ks[k].push(vs)
      else ks[k] = [vs]
      return ks
    }
  }, {})
}

const parse_elem = (html_str) => {
  const template = document.createElement('template')
  template.innerHTML = html_str
  return template.content
}

const open = (collapsible) => {
  if (collapsible.style.display  === 'none') {
    collapsible.style.display = 'block'
    return true
  }
  else return false
}

const close = (collapsible) => {
  if (collapsible.style.display === 'block') {
    collapsible.style.display = 'none'
    return true
  }
  else return false
}
