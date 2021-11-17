function loadSearch(entries, authors, topics, keywords) {
    var entryIndex = new FlexSearch({
        encode: "advanced",
        tokenize: "forward",
        bool: "or",
        doc: {
            id: "id",
            field: ["title", "abstract", "date", "authors"],
        },
    });

    var authorIndex = new FlexSearch({
        encode: "advanced",
        tokenize: "forward",
        doc: {
            id: "id",
            field: "name",
        },
    });

    var topicIndex = new FlexSearch({
        encode: "icase",
        tokenize: "forward",
        doc: {
            id: "id",
            field: "name",
        },
    });

    var suggestIndex = new FlexSearch({
        encode: "icase",
        tokenize: "forward",
        doc: {
            id: "id",
            field: "keyword",
        },
    });

    var indices = {
        entry: entryIndex,
        author: authorIndex,
        topic: topicIndex,
        suggest: suggestIndex,
    };

    indices["entry"].add(entries);
    indices["author"].add(authors);
    indices["topic"].add(topics);
    indices["suggest"].add(keywords);

    var memoQueryFindFacts = memoizer(queryFindFacts);
    const input = document.getElementById("searchInput");

    var searchTerm = input.value;
    if (searchTerm) {
        executeSearch(indices, searchTerm);
        memoQueryFindFacts(searchTerm).then((results) =>
            populateFindFactsResults(searchTerm, results)
        );
    }

    input.addEventListener("keyup", function (event) {
        switch (event.key) {
            case "Enter":
            case "Up":
            case "ArrowUp":
            case "Down":
            case "ArrowDown":
            case "Left":
            case "ArrowLeft":
            case "Right":
            case "ArrowRight":
            case "Escape":
                break;
            default:
                if (this.value && this.value.length > 1) {
                    executeSearch(indices, this.value);
                } else {
                    clearResults();
                }
        }
    });

    input.addEventListener("keyup", debounce(() => {
        var searchTerm = input.value;
        if (searchTerm && searchTerm.length > 2) {
            memoQueryFindFacts(searchTerm).then((results) =>
                populateFindFactsResults(searchTerm, results)
            );
        }
    }, 300));

    input.addEventListener("keydown", function (event) {
        switch (event.key) {
            case "Enter":
                event.preventDefault(); // prevent the form from being submitted
                handleSubmit(this.value);
                break;
            default:
        }
    });

    async function queryFindFacts(searchTerm) {
        var body = '{"filters":[{"field":"SourceCode","filter":{"Term":{"inner":"';
        body += searchTerm + '"}}}],';
        body += '"fields":["Command","ConstantTypeFacet","Kind","SourceTheoryFacet"],';
        body += '"maxFacets":5}';

        const response = await fetch(
            "https://search.isabelle.in.tum.de/v1/default_Isabelle2021_AFP2021/facet",
            {
                method: "POST",
                headers: {
                    "Content-Type": "application/json",
                    accept: "application/json",
                },
                body: body,
            }
        );
        const data = await response.json();
        return data["Kind"];
    }

    function debounce(callback, wait) {
        let timeout;
        return (...args) => {
            clearTimeout(timeout);
            timeout = setTimeout(function () {
                callback.apply(this, args);
            }, wait);
        };
    }

    function memoizer(fun) {
        let cache = {};
        return function (n) {
            if (cache[n] != undefined) {
                return cache[n];
            } else {
                let result = fun(n);
                cache[n] = result;
                return result;
            }
        };
    }
}

function executeSearch(indices, searchQuery) {
    var entryResults = indices["entry"].search({
        query: searchQuery,
        limit: 16,
    });

    var topicResults = indices["topic"].search({
        query: searchQuery,
        limit: 5,
    });

    var authorResults = indices["author"].search({
        query: searchQuery,
        limit: 5,
    });

    var suggestResults = indices["suggest"].search({
        query: searchQuery,
        limit: 10,
    });

    if (entryResults.length > 0) {
        populateResults(entryResults, searchQuery, indices);
    } else {
        setInnerHTMLOfID("search-results", "<p>No results</p>");
    }

    if (authorResults.length > 0) {
        populateSmallResults(authorResults, searchQuery, "author", indices);
    } else {
        setInnerHTMLOfID("author-results", "<p>No results</p>");
    }

    if (topicResults.length > 0) {
        populateSmallResults(topicResults, searchQuery, "topic", indices);
    } else {
        setInnerHTMLOfID("topic-results", "<p>No results</p>");
    }

    if (!(suggestResults.length === 1 && suggestResults[0].keyword === searchQuery)) {
        filterAutocomplete(suggestResults);
    } else {
        filterAutocomplete();
    }
}

function populateResults(results, searchQuery, indices, all = false) {
    if (searchQuery.length < 3) {
        setInnerHTMLOfID("find-facts-results", "");
    } else {
        setInnerHTMLOfID("find-facts-results", "...");
    }

    const resultsTable = document.getElementById("search-results");

    setInnerHTMLOfID("search-results", "");

    var limit = all ? results.length : 15;

    results.slice(0, limit).forEach(function (result, resultKey) {
        var topics = [];

        result.topics.forEach((value, key) => {
            topics[key] = "<a href=/topics/" + result.topic_links[key] + ">" + value + "</a>";
        });

        var topicString = niceList(topics);
        var authorString = niceList(result.authors);

        var title = result.title;
        var link = result.shortname.toLowerCase();
        var shortname = result.shortname;
        var abstract = result.abstract;
        var used_by = result.used_by;
        var year = result.date.substring(0, 4);

        var output = `<div id="summary-${resultKey}">
  <div class='title'>
    <a href="/entries/${link}">${title}</a>
    <a download href="https://isa-afp.org/release/afp-${shortname}-current.tar.gz">Download</a>
  </div>
  <div class='subtitle'>
    ${authorString ? `<p>${authorString}</p>` : ""}
    ${year ? `<p>${year}</p>` : ""}
  </div>
  <div class="abstract mathjax_process">${abstract}</div>
    ${ used_by
        ? `<div>Used by <a href="/dependencies/${link}">${used_by}</a> | ${
                topicString ? `${topicString} ` : ""
            }</div>`
        : topicString ? `<div>${topicString}</div>` : ""
    } 
</div>`;

        resultsTable.insertAdjacentHTML("beforeend", output);
    });

    if (results.length > 15 && !all) {
        var btn = document.createElement("button");
        btn.innerHTML = "Show all results";

        btn.addEventListener("click", function () {
            var entryResults = indices["entry"].search({
                query: searchQuery,
            });

            populateResults(entryResults, searchQuery, indices, true);
        });

        resultsTable.appendChild(btn);
    }

    new Mark(resultsTable).mark(searchQuery);

    function niceList(topics) {
        if (topics.length <= 2) {
            topicString = topics.join(" and ");
        } else {
            topicString =
                topics.slice(0, -1).join(", ") + " and " + topics[topics.length - 1];
        }
        return topicString;
    }
}

function clearResults() {
    setInnerHTMLOfID("author-results", "");
    setInnerHTMLOfID("topic-results", "");
    setInnerHTMLOfID("find-facts-results", "");
    setInnerHTMLOfID("search-results", "<p>Please enter a search term above</p>");
}

function populateSmallResults(results, searchQuery, key, indices, all = false) {
    const maxResults = 4;
    setInnerHTMLOfID(key + "-results", "");

    var resultsTable = document.getElementById(key + "-results");

    var limit = all ? results.length : maxResults;
    var list = document.createElement("ul");

    results.slice(0, limit).forEach((result, resultKey) => {
        var listElement = document.createElement("li");
        var anchor = document.createElement("a");
        anchor.href = result.link;
        anchor.innerHTML = result.name;
        listElement.appendChild(anchor);
        list.appendChild(listElement);
    });

    resultsTable.insertAdjacentElement("beforeend", list);

    if (results.length > maxResults && !all) {
        const btn = document.createElement("button");
        btn.innerHTML = "Show all";

        btn.addEventListener("click", function () {
            var entryResults = indices[key].search({
                query: searchQuery,
            });

            populateSmallResults(entryResults, searchQuery, key, indices, true);
        });

        resultsTable.insertAdjacentElement("beforeend", btn);
    }

    new Mark(resultsTable).mark(searchQuery);
}

function populateFindFactsResults(searchTerm, data) {
    var resultsElement = document.getElementById("find-facts-results");
    if (Object.keys(data).length !== 0 && resultsElement) {
        let urlPrefix =
            'https://search.isabelle.in.tum.de/#search/default_Isabelle2021_AFP2021?q={"term":"';
        urlPrefix += searchTerm + '","facets":{"Kind":["';
        const urlSuffix = '"]}}';

        var list = document.createElement("ul");

        Object.entries(data).forEach(([name, count]) => {
            var listElement = document.createElement("li");
            var anchor = document.createElement("a");
            anchor.href = urlPrefix + name + urlSuffix;
            anchor.target = "_blank";
            anchor.rel = "noreferrer noopener";
            anchor.innerHTML = count + " " + name + "s";
            listElement.appendChild(anchor);
            list.appendChild(listElement);
        });

        setInnerHTMLOfID("find-facts-results", "");
        resultsElement.insertAdjacentElement("beforeend", list);
    } else {
        setInnerHTMLOfID("find-facts-results", "<p>No results</p>");
    }
}

function handleSubmit(value) {
    if (typeof history.pushState !== "undefined") {
        history.pushState({}, "Search the Archive - " + value, "?s=" + value);
    } else {
        var url = "TODO";
        window.location.assign(url);
    }
}

// Autocomplete ------------------------------------------------------------------------

function filterAutocomplete(values) {
    const list = document.getElementById("autocomplete");
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

function setInnerHTMLOfID(id, str) {
    const elem = document.getElementById(id);
    if (elem) {
        elem.innerHTML = str;
    } else {
        console.log("Failed to find:", id, "for innerHTML. Would have set it to", str);
    }
}

document.addEventListener("DOMContentLoaded", function () {
    var input = document.getElementById("searchInput");
    var urlQuery = param("s");
    if (urlQuery) {
        input.value = urlQuery;
    }
    input.focus();

    document.getElementById("searchButton").addEventListener("click", () => {
        handleSubmit(document.getElementById("searchInput").value);
    });

    Promise.all([
        fetch("/index.json"),
        fetch("/authors/index.json"),
        fetch("/topics/index.json"),
        fetch("/data/keywords.json"),
    ])
        .then(function (responses) {
            // Get a JSON object from each of the responses
            return Promise.all(responses.map((response) => response.json()));
        })
        .then((data) => loadSearch(...data));

    function param(name) {
        return decodeURIComponent(
            (location.search.split(name + "=")[1] || "").split("&")[0]
        ).replace(/\+/g, " ");
    }
});
