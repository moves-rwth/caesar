Prism.languages.dafny = {
	'comment': {
		pattern: /\/\/.*|\/\*[\s\S]*?(?:\*\/|$)/,
		greedy: true
	},
	'string': {
		pattern: /"(?:\\.|[^"\\])*"/,
		greedy: true
	},
	'attribute': {
		pattern: /\{:[^{}]*\}/,
		inside: {
			'keyword': /\b(?:axiom|trigger)\b/,
			'punctuation': /[{}:]/
		}
	},
	'keyword': /\b(?:abstract|assert|assume|break|by|calc|case|class|const|constructor|continue|datatype|decreases|else|ensures|exists|false|for|forall|function|ghost|if|in|include|invariant|import|is|label|lemma|match|method|modifies|module|nat|new|null|old|predicate|print|reads|refines|requires|return|returns|reveals|seq|set|static|then|trait|true|type|var|while|witness)\b/,
	'boolean': /\b(?:false|true)\b/,
	'number': /-?\b\d+(?:\.\d+)?\b/,
	'operator': /&&|\|\||==>|:=|==|!=|<=|>=|<|>|\+|-|\*|\/|%|!/,
	'punctuation': /[()[\]{}.,;:]/,
};

Prism.languages.dfy = Prism.languages.dafny;
