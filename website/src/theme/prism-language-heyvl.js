(function (Prism) {
  // Expand nested comments to four levels, following Prism's Rust grammar.
  let blockComment = /\/\*(?:[^*/]|\*(?!\/)|\/(?!\*)|<self>)*(?:\*\/|$)/.source;
  for (let i = 0; i < 2; i++) {
    blockComment = blockComment.replace(/<self>/g, () => blockComment);
  }
  blockComment = blockComment.replace(/<self>/g, '(?!)');

  Prism.languages.heyvl = {
    'comment': {
      pattern: RegExp(/\/\/[^\r\n]*|/.source + blockComment),
      greedy: true
    },
    'string': {
      pattern: /"[^"]*(?:"|$)/,
      greedy: true
    },
    'annotation': {
      pattern: /@[ \t]*[_a-zA-Z][_a-zA-Z0-9']*/,
      alias: 'keyword'
    },
    'keyword': [
      {
        pattern: /(^|[^\\_a-zA-Z0-9'])(?:var|(?:co)?assume|(?:co)?assert|(?:co)?negate|(?:co)?validate|if|else|(?:co)?proc|pre|post|(?:co)?compare|tick|reward|weigh|while|(?:co)?havoc|domain|func|axiom|label)(?![_a-zA-Z0-9'])/,
        lookbehind: true
      },
      /->/
    ],
    'boolean': {
      pattern: /(^|[^\\_a-zA-Z0-9'])(?:false|true)(?![_a-zA-Z0-9'])/,
      lookbehind: true
    },
    'number': [
      {
        // Keep integer fractions together without consuming part of a decimal denominator.
        pattern: /(^|[^\\_a-zA-Z0-9'])(?:[0-9]+\/[0-9]+(?![0-9.])|[0-9]+(?:\.[0-9]+)?)/,
        lookbehind: true
      },
      /∞|\\infty(?![_a-zA-Z0-9'])/
    ],
    'builtin': [
      {
        pattern: /(^|[^\\_a-zA-Z0-9'])(?:Bool|Int|UInt|Uint|Real|UReal|EUReal|Realplus|ite|let|flip)(?![_a-zA-Z0-9'])/,
        lookbehind: true
      },
      /\[\]/
    ],
    'operator': [
      {
        pattern: /(^|[^\\_a-zA-Z0-9'])(?:forall|exists|inf|sup)(?![_a-zA-Z0-9'])/,
        lookbehind: true
      },
      /\\(?:cap|cup|oplus)(?![_a-zA-Z0-9'])/,
      /![ \t]*\?|==>|<==|!=|==|<=|>=|&&|\|\||[!?~+*%<>=→←↘↖⊓⊔⊕-]|\/(?![/*])|\[(?!\])|\]/
    ],
    'punctuation': /[{}(),:;.]/
  };
}(Prism));
