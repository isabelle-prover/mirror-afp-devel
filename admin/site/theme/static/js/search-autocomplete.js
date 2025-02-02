/* constants */

const ID_AUTOCOMPLETE = "autocomplete"

const get_suggest_index = (keywords) =>
{
  const index = new FlexSearch.Document({
    encoder: "icase",
    tokenize: "forward",
    document: {
      index: "keyword",
      store: true,
    }
  });
  keywords.forEach(keyword => index.add(keyword))
  return index
}

const add_suggestions = (index, query) =>
{
  const suggest_results = index.search(query, { pluck: 'keyword', enrich: true }).map(d => d.doc)

  if (!(suggest_results.length === 1 && suggest_results[0].keyword === query)) {
    filter_autocomplete(suggest_results);
  } else {
    filter_autocomplete();
  }
}

function filter_autocomplete(values)
{
  const list = document.getElementById(ID_AUTOCOMPLETE);
  if (list) {
    if (values) {
      let i = 0;
      for (let value of values) {
        let elem = document.createElement("option");
        elem.value = value.keyword;
        if (i < list.childNodes.length) {
          list.childNodes[i].replaceWith(elem);
          i++;
        } else {
          list.appendChild(elem);
        }
      }
      if (values.length < list.childNodes.length) {
        for (let j = 0; j < list.childNodes.length - values.length; j++) {
          list.removeChild(list.lastChild);
        }
      }
    } else {
      while (list.firstChild) {
        list.removeChild(list.lastChild);
      }
    }
  }
}
