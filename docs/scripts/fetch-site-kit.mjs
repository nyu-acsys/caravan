import { spawnSync } from 'node:child_process'
import { lstatSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, realpathSync, renameSync, rmSync, writeFileSync } from 'node:fs'
import { dirname, isAbsolute, join, relative, resolve, sep } from 'node:path'
import { fileURLToPath, pathToFileURL } from 'node:url'

const defaultDocsRoot = fileURLToPath(new URL('../', import.meta.url))
const defaultRepository = 'https://github.com/nyu-acsys/raven.git'
const packageName = '@nyu-acsys/docs-kit'

function run(command, args, cwd) {
  const result = spawnSync(command, args, {
    cwd, encoding: 'utf8', shell: false, timeout: 60000, maxBuffer: 4 * 1024 * 1024,
    env: { ...process.env, GIT_TERMINAL_PROMPT: '0' }
  })
  if (result.error) throw new Error(`Could not run ${command}: ${result.error.message}`, { cause: result.error })
  if (result.status !== 0) throw new Error(`${command} failed: ${result.stderr.trim() || `exit ${result.status}`}`)
  return result.stdout.trim()
}

function inside(root, path) {
  const name = relative(root, path)
  return name === '' || (!isAbsolute(name) && name !== '..' && !name.startsWith(`..${sep}`))
}

function validatePackage(directory) {
  function ordinaryFiles(path) {
    const stat = lstatSync(path)
    if (stat.isDirectory()) {
      for (const entry of readdirSync(path)) ordinaryFiles(join(path, entry))
    } else if (!stat.isFile()) {
      throw new Error(`Site kit contains a non-regular file: ${relative(directory, path)}`)
    }
  }
  ordinaryFiles(directory)
  const manifest = JSON.parse(readFileSync(join(directory, 'package.json'), 'utf8'))
  if (manifest.name !== packageName) throw new Error(`Expected the ${packageName} package`)
}

/** Fetch only the committed site-kit subtree, preserving the previous installation on failure. */
export function fetchSiteKit({ docsRoot = defaultDocsRoot, source, repository = defaultRepository } = {}) {
  const root = realpathSync(docsRoot)
  if (!lstatSync(root).isDirectory()) throw new Error('The documentation root must be a directory')
  const revision = readFileSync(join(root, 'SITE_KIT_REVISION'), 'utf8').trim()
  if (!/^[a-f0-9]{40}$/.test(revision)) throw new Error('SITE_KIT_REVISION must contain a full lowercase commit SHA')
  const directory = join(root, '.site-kit')
  const installed = lstatSync(directory, { throwIfNoEntry: false })
  if (installed) {
    if (!installed.isDirectory()) throw new Error('The site-kit destination must be an ordinary directory')
    const marker = lstatSync(join(directory, '.revision'), { throwIfNoEntry: false })
    if (!marker?.isFile() || !/^[a-f0-9]{40}$/.test(readFileSync(join(directory, '.revision'), 'utf8').trim())) {
      throw new Error('Refusing to replace an unmanaged site-kit directory')
    }
    if (readFileSync(join(directory, '.revision'), 'utf8').trim() === revision) {
      validatePackage(directory)
      return { revision, reused: true, directory }
    }
  }
  const local = source === undefined ? undefined : realpathSync(resolve(source))
  if (local && !lstatSync(local).isDirectory()) throw new Error('The source checkout must be a directory')
  if (local && inside(directory, local)) throw new Error('The source checkout must be outside the site-kit destination')
  const temporary = mkdtempSync(join(root, '.site-kit-fetch-'))
  let retainPrevious = false
  try {
    let checkout = local
    if (!checkout) {
      checkout = join(temporary, 'repository')
      mkdirSync(checkout)
      run('git', ['init', '--quiet'], checkout)
      run('git', ['remote', 'add', 'origin', repository], checkout)
      run('git', ['config', 'remote.origin.promisor', 'true'], checkout)
      run('git', ['config', 'remote.origin.partialclonefilter', 'blob:none'], checkout)
      run('git', ['fetch', '--quiet', '--depth=1', '--filter=blob:none', '--no-tags', 'origin', revision], checkout)
    }
    if (run('git', ['cat-file', '-t', revision], checkout) !== 'commit') {
      throw new Error('The pinned site-kit revision must identify a commit')
    }
    const archive = join(temporary, 'site-kit.tar')
    run('git', ['archive', '--format=tar', `--output=${archive}`, `${revision}:docs/site-kit`], checkout)
    const staged = join(temporary, 'package')
    mkdirSync(staged)
    run('tar', ['-xf', archive, '-C', staged], root)
    validatePackage(staged)
    writeFileSync(join(staged, '.revision'), revision + '\n')
    const backup = join(temporary, 'previous')
    if (installed) renameSync(directory, backup)
    try {
      renameSync(staged, directory)
    } catch (error) {
      if (installed) {
        try { renameSync(backup, directory) }
        catch (restoreError) {
          retainPrevious = true
          throw new Error(`Could not restore the previous site kit; it remains at ${backup}`, { cause: restoreError })
        }
      }
      throw error
    }
    return { revision, reused: false, directory }
  } finally {
    if (!retainPrevious) rmSync(temporary, { recursive: true, force: true })
  }
}

if (process.argv[1] && pathToFileURL(resolve(process.argv[1])).href === import.meta.url) {
  const args = process.argv.slice(2)
  if (args.length !== 0 && !(args.length === 2 && args[0] === '--source')) {
    throw new Error('Usage: node scripts/fetch-site-kit.mjs [--source PATH]')
  }
  const result = fetchSiteKit({ source: args[1] })
  console.log(`site-kit: ${result.reused ? 'using' : 'fetched'} ${result.revision}`)
}
