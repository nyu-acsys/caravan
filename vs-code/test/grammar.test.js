const assert = require('node:assert/strict');
const fs = require('node:fs');
const path = require('node:path');
const { test } = require('node:test');
const { Registry, parseRawGrammar, INITIAL } = require('vscode-textmate');
const { loadWASM, OnigScanner, OnigString } = require('vscode-oniguruma');

const root = path.join(__dirname, '..');
const files = {
  'source.caravan.spec': 'spec', 'source.caravan.proof': 'proof',
  'caravan.ocaml.injection': 'ocaml-injection'
};
const wasm = loadWASM(fs.readFileSync(require.resolve('vscode-oniguruma/release/onig.wasm')));
const ocaml = scopeName => ({
  scopeName,
  patterns: [
    { name: 'comment.block.ocaml', begin: '\\(\\*', end: '\\*\\)', patterns: [{ include: '$self' }] },
    { name: 'string.quoted.double.ocaml', begin: '"', end: '"', patterns: [{ match: '\\\\.', name: 'constant.character.escape.ocaml' }] },
    { name: 'keyword.other.ocaml', match: '\\b(?:val|external)\\b' }
  ]
});
async function grammar(scope) {
  await wasm;
  const registry = new Registry({
    onigLib: Promise.resolve({ createOnigScanner: patterns => new OnigScanner(patterns), createOnigString: value => new OnigString(value) }),
    loadGrammar: async name => {
      if (files[name]) {
        const file = path.join(root, 'syntaxes', files[name] + '.tmLanguage.json');
        return parseRawGrammar(fs.readFileSync(file, 'utf8'), file);
      }
      // Exercise injection precedence against the host's comment and string rules.
      if (name === 'source.ocaml' || name === 'source.ocaml.interface') return ocaml(name);
      return null;
    },
    getInjections: name => ['source.ocaml', 'source.ocaml.interface'].includes(name) ? ['caravan.ocaml.injection'] : []
  });
  return registry.loadGrammar(scope);
}
function tokenize(grammar, text) {
  let stack = INITIAL;
  return text.split('\n').map(line => {
    const result = grammar.tokenizeLine(line, stack);
    stack = result.ruleStack;
    return { line, tokens: result.tokens };
  });
}
function scopes(line, needle) {
  const index = line.line.indexOf(needle);
  assert.notEqual(index, -1);
  return line.tokens.find(token => token.startIndex <= index && token.endIndex > index).scopes;
}
const has = (line, text, scope) => assert.ok(scopes(line, text).includes(scope), `${text}: ${scopes(line, text).join(', ')}`);
const lacks = (line, text, scope) => assert.ok(!scopes(line, text).includes(scope), `${text}: ${scopes(line, text).join(', ')}`);

test('all and only specification lexer keywords receive categorized Caravan scopes', async () => {
  const source = fs.readFileSync(path.join(root, '../lib/spec/spec_lexer.mll'), 'utf8').split('(* to translate')[0];
  const words = [...source.matchAll(/"([a-z]+)",\s*(?:[A-Z]|OP)/g)].map(match => match[1]);
  assert.ok(words.length > 40);
  const g = await grammar('source.caravan.proof');
  for (const word of words) {
    const [line] = tokenize(g, `${word} ${word}_suffix '${word} ${word}'`);
    assert.ok(scopes(line, word).some(scope => /^(keyword\.(control|other)|storage\.(type|modifier)|constant\.language)\.caravan$/.test(scope)), word);
    for (const identifier of [`${word}_suffix`, `${word}'`]) {
      assert.ok(!scopes(line, identifier).some(scope => /^(keyword\.(control|other)|storage\.(type|modifier)|constant\.language)\.caravan$/.test(scope)), identifier);
    }
    has(line, `'${word}`, 'storage.type.caravan');
  }
  const spec = JSON.parse(fs.readFileSync(path.join(root, 'syntaxes/spec.tmLanguage.json'), 'utf8'));
  const highlighted = spec.repository.keywords.patterns.flatMap(rule => rule.match.match(/\(\?:([^)]*)\)/)[1].split('|'));
  assert.deepEqual(highlighted.sort(), words.sort());
});

test('proof files share lexical rules and retain OCaml fallback', async () => {
  const lines = tokenize(await grammar('source.caravan.proof'), 'val x : int\nrequires "ensures \\" continues"\n(* requires (* invariant *) ensures *)\nforall x. x = 0xF');
  has(lines[0], 'val', 'keyword.other.ocaml');
  has(lines[1], 'requires', 'keyword.other.caravan');
  has(lines[1], 'ensures', 'string.quoted.double.caravan');
  lacks(lines[1], 'continues', 'keyword.other.caravan');
  has(lines[2], 'invariant', 'comment.block.caravan');
  lacks(lines[2], 'ensures', 'keyword.other.caravan');
  has(lines[3], 'forall', 'keyword.control.caravan');
  has(lines[3], '0xF', 'constant.numeric.caravan');
});

for (const scope of ['source.ocaml', 'source.ocaml.interface']) {
  test(`${scope}: annotations nest comments and protect terminators in strings`, async () => {
    const lines = tokenize(await grammar(scope), '(*@ requires true\n(* nested (* ensures *) comment *)\nensures "*) requires"\nreturns false *)\nval outside : int\n(* ordinary (*@ requires *) *)\n"(*@ ensures *)"');
    has(lines[0], 'requires', 'keyword.other.caravan');
    has(lines[1], 'ensures', 'comment.block.caravan');
    lacks(lines[1], 'ensures', 'keyword.other.caravan');
    has(lines[2], 'ensures', 'keyword.other.caravan');
    has(lines[2], 'requires', 'string.quoted.double.caravan');
    has(lines[3], 'returns', 'keyword.other.caravan');
    has(lines[4], 'val', 'keyword.other.ocaml');
    lacks(lines[4], 'outside', 'meta.embedded.block.caravan');
    lacks(lines[5], 'requires', 'keyword.other.caravan');
    lacks(lines[6], 'ensures', 'keyword.other.caravan');
  });
}

test('shared literal rules handle characters, type variables, and specification primitives', async () => {
  const [line] = tokenize(await grammar('source.caravan.proof'), "'a' '\\n' 'value `predicate_name` ~fraction Set.of_predicate 0b101 42i");
  has(line, "'a'", 'string.quoted.single.caravan');
  has(line, "'\\n'", 'string.quoted.single.caravan');
  has(line, "'value", 'storage.type.caravan');
  has(line, '`predicate_name`', 'entity.name.function.caravan');
  has(line, '~fraction', 'support.function.caravan');
  has(line, 'Set.of_predicate', 'support.function.caravan');
  has(line, '0b101', 'constant.numeric.caravan');
  has(line, '42i', 'constant.numeric.caravan');
});

test('specification categories follow Raven concepts without changing host OCaml syntax', async () => {
  const [line] = tokenize(await grammar('source.caravan.proof'), 'requires ensures invariant variant predicate view lemma action pure assert fold unfold forall exists true false');
  for (const word of ['requires', 'ensures', 'invariant', 'variant']) has(line, word, 'keyword.other.caravan');
  for (const word of ['predicate', 'view', 'lemma', 'action']) has(line, word, 'storage.type.caravan');
  has(line, 'pure', 'storage.modifier.caravan');
  for (const word of ['assert', 'fold', 'unfold', 'forall', 'exists']) has(line, word, 'keyword.control.caravan');
  for (const word of ['true', 'false']) has(line, word, 'constant.language.caravan');
  const [host] = tokenize(await grammar('source.ocaml'), 'val requires : bool');
  has(host, 'val', 'keyword.other.ocaml');
  lacks(host, 'requires', 'keyword.other.caravan');
});
