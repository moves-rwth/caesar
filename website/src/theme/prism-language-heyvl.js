Prism.languages.heyvl = {
	'keyword': /\b(var|(co)?assume|(co)?assert|(co)?negate|(co)?validate|if|else|(co)?proc|pre|post|(co)?compare|tick|reward|while|(co)?havoc|domain|func|axiom)\b|@\w+/,
	'boolean': /\b(?:false|true)\b/,
	'number': /-?\b\d+(?:\.\d+)?(?:e[+-]?\d+)?\b/i,
	'comment': {
		pattern: /\/\/.*|\/\*[\s\S]*?(?:\*\/|$)/,
		greedy: true
	},
	'punctuation': /[{}[\],]/,
	'operator': /[*\/%^!=]=?|\+[=+]?|-[=-]?|\|[=|]?|&(?:=|&|\^=?)?|>(?:>=?|=)?|<(?:<=?|=|-)?|:=|\.\.\.|forall|exists|\?/,
	'builtin': /\b(Bool|Int|UInt|Real|UReal|EUReal|Type|ite|let)\b/
};
