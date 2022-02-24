
/* utilities */

const CLASS_COLLAPSED = 'collapsed'
const CLASS_COLLAPSIBLE = 'collapsible'
const CLASS_INVERTIBLE = 'invertible'
const CLASS_COLLAPSE_CONTAINER = 'collapse-container'

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

const is_collapsed = (e) => {
  return e.classList.contains(CLASS_COLLAPSED)
}

const open = (collapsible) => {
  if (collapsible.classList.contains(CLASS_COLLAPSED)) {
    collapsible.classList.remove(CLASS_COLLAPSED)
    return true
  }
  else return false
}

const collapse = (collapsible) => {
  if (!collapsible.classList.contains(CLASS_COLLAPSED)) {
    collapsible.classList.add(CLASS_COLLAPSED)
    return true
  }
  else return false
}

const escape_html = (html) => {
  return html.replace(/[&<>"']/g, function(m) {
    switch (m) {
      case '&':
        return '&amp;'
      case '<':
        return '&lt;'
      case '>':
        return '&gt;'
      case '"':
        return '&quot;'
      case "'":
        return '&#39;'
    }
  })
}