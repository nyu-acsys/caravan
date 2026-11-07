import assert from 'node:assert/strict'
import { spawnSync } from 'node:child_process'
import { cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, symlinkSync, writeFileSync } from 'node:fs'
import { tmpdir } from 'node:os'
import { dirname, join } from 'node:path'
import { fileURLToPath, pathToFileURL } from 'node:url'
import test from 'node:test'
import { fetchSiteKit } from '../scripts/fetch-site-kit.mjs'

function fixture(t) {
  const root = mkdtempSync(join(tmpdir(), 'site kit bootstrap '))
  t.after(() => rmSync(root, { recursive: true, force: true }))
  const repository = join(root, 'raven')
  const docsRoot = join(root, 'docs')
  mkdirSync(join(repository, 'docs/site-kit'), { recursive: true })
  mkdirSync(join(repository, 'empty-hooks'))
  mkdirSync(docsRoot)
  const git = (...args) => {
    const result = spawnSync('git', args, { cwd: repository, encoding: 'utf8', shell: false })
    assert.equal(result.status, 0, result.stderr)
    return result.stdout.trim()
  }
  git('init', '--quiet')
  const commit = version => {
    writeFileSync(join(repository, 'docs/site-kit/package.json'), JSON.stringify({ name: '@nyu-acsys/docs-kit', version }))
    writeFileSync(join(repository, 'docs/site-kit/content.txt'), version)
    writeFileSync(join(repository, 'unrelated.txt'), 'Not part of the package')
    git('add', 'docs/site-kit', 'unrelated.txt')
    git('-c', 'user.name=Docs test', '-c', 'user.email=docs@example.invalid', '-c', 'commit.gpgsign=false', '-c', `core.hooksPath=${join(repository, 'empty-hooks')}`, 'commit', '--quiet', '-m', version)
    return git('rev-parse', 'HEAD')
  }
  const first = commit('1.0.0')
  const pin = revision => writeFileSync(join(docsRoot, 'SITE_KIT_REVISION'), revision + '\n')
  pin(first)
  const contents = () => readFileSync(join(docsRoot, '.site-kit/content.txt'), 'utf8')
  return { root, repository, docsRoot, git, commit, first, pin, contents }
}

test('local bootstrap reads the pinned commit rather than dirty checkout files', t => {
  const f = fixture(t)
  writeFileSync(join(f.repository, 'docs/site-kit/content.txt'), 'dirty working tree')
  writeFileSync(join(f.repository, 'docs/site-kit/untracked.txt'), 'untracked')
  const result = fetchSiteKit({ docsRoot: f.docsRoot, source: f.repository })
  assert.equal(result.revision, f.first)
  assert.equal(result.reused, false)
  assert.equal(f.contents(), '1.0.0')
  assert.equal(existsSync(join(result.directory, 'untracked.txt')), false)
  assert.equal(existsSync(join(result.directory, 'unrelated.txt')), false)
  assert.equal(existsSync(join(result.directory, '.git')), false)
  assert.deepEqual(readdirSync(f.docsRoot).sort(), ['.site-kit', 'SITE_KIT_REVISION'])
  assert.equal(fetchSiteKit({ docsRoot: f.docsRoot, source: join(f.root, 'missing') }).reused, true)
})

test('pin changes replace the package and failed revisions preserve the previous copy', t => {
  const f = fixture(t)
  fetchSiteKit({ docsRoot: f.docsRoot, source: f.repository })
  const second = f.commit('2.0.0')
  f.pin(second)
  assert.equal(fetchSiteKit({ docsRoot: f.docsRoot, source: f.repository }).reused, false)
  assert.equal(f.contents(), '2.0.0')
  f.pin('0'.repeat(40))
  assert.throws(() => fetchSiteKit({ docsRoot: f.docsRoot, source: f.repository }), /git failed/)
  assert.equal(f.contents(), '2.0.0')
  assert.equal(readFileSync(join(f.docsRoot, '.site-kit/.revision'), 'utf8').trim(), second)
  assert.equal(readdirSync(f.docsRoot).some(name => name.startsWith('.site-kit-fetch-')), false)
})

test('remote mode fetches the exact pin and stores only the package subtree', t => {
  const f = fixture(t)
  f.commit('2.0.0')
  const result = fetchSiteKit({ docsRoot: f.docsRoot, repository: f.repository })
  assert.equal(result.revision, f.first)
  assert.equal(f.contents(), '1.0.0')
  assert.equal(existsSync(join(result.directory, 'unrelated.txt')), false)
  assert.equal(existsSync(join(result.directory, '.git')), false)
})

test('filtered remote fetches lazily obtain the package blobs from their promisor remote', t => {
  const f = fixture(t)
  f.git('config', 'uploadpack.allowFilter', 'true')
  f.git('config', 'uploadpack.allowAnySHA1InWant', 'true')
  const blob = f.git('rev-parse', `${f.first}:docs/site-kit/content.txt`)
  const traceFile = join(f.root, 'packets.log')
  const previousTrace = process.env.GIT_TRACE_PACKET
  process.env.GIT_TRACE_PACKET = traceFile
  try {
    const result = fetchSiteKit({ docsRoot: f.docsRoot, repository: pathToFileURL(f.repository).href })
    assert.equal(result.revision, f.first)
    assert.equal(f.contents(), '1.0.0')
  } finally {
    if (previousTrace === undefined) delete process.env.GIT_TRACE_PACKET
    else process.env.GIT_TRACE_PACKET = previousTrace
  }
  const trace = readFileSync(traceFile, 'utf8')
  assert.ok(trace.includes('filter blob:none'))
  assert.ok(trace.includes(`want ${blob}`), 'The archive must fetch the omitted content blob lazily')
})

test('CLI locates its pin and destination independently of the current directory', t => {
  const f = fixture(t)
  const script = join(f.docsRoot, 'scripts/fetch-site-kit.mjs')
  mkdirSync(dirname(script))
  cpSync(fileURLToPath(new URL('../scripts/fetch-site-kit.mjs', import.meta.url)), script)
  const result = spawnSync(process.execPath, [script, '--source', f.repository], {
    cwd: f.root, encoding: 'utf8', shell: false
  })
  assert.equal(result.status, 0, result.stderr)
  assert.ok(result.stdout.includes(f.first))
  assert.equal(f.contents(), '1.0.0')
  assert.equal(existsSync(join(f.root, '.site-kit')), false)
})

test('invalid pins and unmanaged destinations fail before replacing user files', t => {
  const f = fixture(t)
  f.pin('main')
  assert.throws(() => fetchSiteKit({ docsRoot: f.docsRoot, source: f.repository }), /full lowercase commit SHA/)
  f.pin(f.first)
  mkdirSync(join(f.docsRoot, '.site-kit'))
  writeFileSync(join(f.docsRoot, '.site-kit/user.txt'), 'preserved')
  assert.throws(() => fetchSiteKit({ docsRoot: f.docsRoot, source: f.repository }), /unmanaged/)
  assert.equal(readFileSync(join(f.docsRoot, '.site-kit/user.txt'), 'utf8'), 'preserved')
})

test('unexpected package contents retain an existing installation', t => {
  const f = fixture(t)
  fetchSiteKit({ docsRoot: f.docsRoot, source: f.repository })
  writeFileSync(join(f.repository, 'docs/site-kit/package.json'), JSON.stringify({ name: 'another-package' }))
  f.git('add', 'docs/site-kit/package.json')
  f.git('-c', 'user.name=Docs test', '-c', 'user.email=docs@example.invalid', '-c', 'commit.gpgsign=false', '-c', `core.hooksPath=${join(f.repository, 'empty-hooks')}`, 'commit', '--quiet', '-m', 'Wrong package')
  f.pin(f.git('rev-parse', 'HEAD'))
  assert.throws(() => fetchSiteKit({ docsRoot: f.docsRoot, source: f.repository }), /Expected the @nyu-acsys\/docs-kit package/)
  assert.equal(f.contents(), '1.0.0')
})

test('a source checkout inside the destination cannot be replaced', t => {
  const f = fixture(t)
  const original = fetchSiteKit({ docsRoot: f.docsRoot, source: f.repository })
  f.pin(f.commit('2.0.0'))
  assert.throws(() => fetchSiteKit({ docsRoot: f.docsRoot, source: original.directory }), /outside the site-kit destination/)
  assert.equal(f.contents(), '1.0.0')
})

test('symlink destinations cannot redirect installation writes', t => {
  const f = fixture(t)
  const outside = join(f.root, 'outside')
  mkdirSync(outside)
  writeFileSync(join(outside, 'keep.txt'), 'preserved')
  try { symlinkSync(outside, join(f.docsRoot, '.site-kit'), process.platform === 'win32' ? 'junction' : 'dir') }
  catch (error) {
    if (error.code === 'EPERM' || error.code === 'EACCES') return t.skip('Symlinks unavailable')
    throw error
  }
  assert.throws(() => fetchSiteKit({ docsRoot: f.docsRoot, source: f.repository }), /ordinary directory/)
  assert.equal(readFileSync(join(outside, 'keep.txt'), 'utf8'), 'preserved')
})
