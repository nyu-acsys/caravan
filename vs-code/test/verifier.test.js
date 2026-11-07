const { test } = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs/promises');
const os = require('node:os');
const path = require('node:path');
const http = require('node:http');
const v = require('../out/client/verifier');
const { systemPath } = require('../out/shared/toolchain');
const manifest = {version:'0.2.0',lsp_protocol:1,min_z3:'4.12.0',ocaml_version:'5.5.0',raven_api_version:1};
test('semver order and manifest compatibility', () => {
  assert.equal(v.compareVersions('v1.2.3','1.2.3'),0);
  assert.equal(v.compareVersions('1.2.3-rc.9','1.2.3-rc.10'),-1);
  assert.equal(v.compareVersions('1.2.3','1.2.3-rc.10'),1);
  assert.throws(()=>v.compareVersions('../x','1.0.0'));
  assert.throws(()=>v.validateManifest({...manifest,lsp_protocol:2}));
  assert.throws(()=>v.validateManifest({...manifest,raven_api_version:0}));
  assert.deepEqual(v.validateManifest(manifest),manifest);
  assert.deepEqual(v.validateManifest({...manifest,build:{revision:'future metadata'}}),manifest);
});
async function fixture(root,m=manifest) {
  await fs.mkdir(path.join(root,'bin'),{recursive:true});
  await fs.mkdir(path.join(root,'lib/ocaml'),{recursive:true});
  await fs.writeFile(path.join(root,'manifest.json'),JSON.stringify(m));
  await fs.writeFile(path.join(root,'lib/ocaml/stdlib.cmi'),'fixture');
  await fs.writeFile(path.join(root,'bin/caravan'),`#!/usr/bin/env node\nif(process.env.OCAMLLIB!==require('path').join(__dirname,'../lib/ocaml'))process.exit(2);console.log(${JSON.stringify(JSON.stringify(m))});\n`,{mode:0o755});
  await fs.writeFile(path.join(root,'bin/z3'),'#!/bin/sh\necho "Z3 version 4.13.0"\n',{mode:0o755});
}
test('resolution respects overrides, floors, tags and bundled channel',
  {skip:process.platform==='win32' && 'Unix executable fixtures; native Windows binaries covered by nativeBundle.test.js'},async()=>{
  const temp=await fs.mkdtemp(path.join(os.tmpdir(),'caravan-test-'));
  try {
    const options={extensionPath:path.join(temp,'ext'),storagePath:temp,channel:'stable'};
    await fixture(path.join(options.extensionPath,'bundled'));
    await fixture(path.join(temp,'verifier/0.1.0'),{...manifest,version:'0.1.0'});
    assert.equal((await v.resolveToolchain(options)).source,'bundled');
    await fixture(path.join(temp,'verifier/0.3.0'),{...manifest,version:'0.3.0'});
    assert.equal((await v.resolveToolchain(options)).manifest.version,'0.3.0');
    assert.equal((await v.resolveToolchain({...options,channel:'tag',version:'v0.1.0'})).manifest.version,'0.1.0');
    assert.equal((await v.resolveToolchain({...options,channel:'bundled'})).source,'bundled');
    assert.deepEqual(await v.resolveToolchain({...options,executable:'opam',arguments:['exec','--','caravan']}),{source:'configured',executable:'opam',arguments:['exec','--','caravan']});
    await fs.writeFile(path.join(temp,'verifier/0.3.0/manifest.json'),'{}');
    assert.equal((await v.resolveToolchain(options)).source,'bundled');
  } finally { await fs.rm(temp,{recursive:true,force:true}); }
});
test('environment keeps toolchain stdlib and solver together',()=>{
  const env=v.toolchainEnvironment('/bundle',{PATH:'/usr/bin',OTHER:'x'});
  assert.equal(env.OCAMLLIB,path.join('/bundle','lib','ocaml'));
  assert.equal(env.PATH,`${path.join('/bundle','bin')}${path.delimiter}/usr/bin`);
  assert.equal(env.OTHER,'x');
});
test('latest metadata skips extension releases and enforces HTTPS by default',async()=>{
  const server=http.createServer((req,res)=>{
    res.setHeader('Content-Type','application/json');
    res.end(JSON.stringify(req.url.startsWith('/releases/')?[
      {tag_name:'vscode-v0.9.0',assets:[]},
      {tag_name:'v0.2.0',assets:[{name:'manifest.json',browser_download_url:`http://127.0.0.1:${server.address().port}/manifest`}]}
    ]:manifest));
  });
  await new Promise(resolve=>server.listen(0,'127.0.0.1',resolve));
  const options={apiBase:`http://127.0.0.1:${server.address().port}`,allowHttpForTests:true};
  try {
    assert.equal((await v.fetchRelease(undefined,options)).tag,'v0.2.0');
    await assert.rejects(v.fetchRelease(undefined,{...options,allowHttpForTests:false}),/HTTPS/);
    const controller=new AbortController();controller.abort();
    await assert.rejects(v.fetchRelease(undefined,{...options,signal:controller.signal}));
  } finally { await new Promise(resolve=>server.close(resolve)); }
});
function archive(entries) {
  const chunks=[];
  for(const [name,contents,mode='0000644'] of entries){
    const data=Buffer.from(contents),h=Buffer.alloc(512);
    h.write(name);h.write(mode,100);h.write('0000000',108);h.write('0000000',116);
    h.write(data.length.toString(8).padStart(11,'0'),124);h.write('00000000000',136);
    h.fill(32,148,156);h.write('0',156);h.write('ustar\0',257);h.write('00',263);
    h.write([...h].reduce((a,b)=>a+b,0).toString(8).padStart(6,'0')+'\0 ',148);
    chunks.push(h,data,Buffer.alloc((512-data.length%512)%512));
  }
  return require('node:zlib').gzipSync(Buffer.concat([...chunks,Buffer.alloc(1024)]));
}
test('installation verifies checksums, archive paths and executable before atomic publication',
  {skip:process.platform==='win32' && 'Unix executable fixtures; native Windows binaries covered by nativeBundle.test.js'},async()=>{
  const manifestBytes=Buffer.from(JSON.stringify(manifest));
  let tar=archive([
    ['manifest.json',manifestBytes],['lib/ocaml/stdlib.cmi','fixture'],
    ['bin/caravan',`#!/usr/bin/env node\nif(process.argv.includes('--manifest'))console.log(${JSON.stringify(JSON.stringify(manifest))});else {const fs=require('fs');if(!process.env.OCAMLLIB.endsWith('/lib/ocaml')||process.argv[2]!=='--shh'||!fs.statSync(process.argv[3]).isFile())process.exit(2); }\n`,'0000755'],
    ['bin/z3','#!/bin/sh\necho "Z3 version 4.13.0"\n','0000755']
  ]);
  let corrupt=false;
  const hash=b=>require('node:crypto').createHash('sha256').update(b).digest('hex');
  const server=http.createServer((req,res)=>{
    if(req.url==='/SHA256SUMS')res.end(`${hash(manifestBytes)}  manifest.json\n${corrupt?'0'.repeat(64):hash(tar)}  caravan-linux-x64.tar.gz\n`);
    else res.end(req.url==='/manifest.json'?manifestBytes:tar);
  });
  await new Promise(resolve=>server.listen(0,'127.0.0.1',resolve));
  const root=await fs.mkdtemp(path.join(os.tmpdir(),'caravan-install-'));
  const url=`http://127.0.0.1:${server.address().port}`;
  const release={tag:'v0.2.0',manifest,assets:new Map(['manifest.json','SHA256SUMS','caravan-linux-x64.tar.gz'].map(n=>[n,`${url}/${n}`]))};
  const options={allowHttpForTests:true,asset:'caravan-linux-x64.tar.gz'};
  try {
    corrupt=true;await assert.rejects(v.installRelease(release,root,options),/Checksum/);
    await assert.rejects(fs.access(path.join(root,'verifier/0.2.0')));
    corrupt=false;
    const safeTar=tar;tar=archive([['../escape','unsafe']]);
    await assert.rejects(v.installRelease(release,root,options),/Unsafe/);
    tar=archive([['manifest.json',manifestBytes],['bin/caravan',`#!/bin/sh\necho '${JSON.stringify(manifest)}'\n`,'0000755']]);
    await assert.rejects(v.installRelease(release,root,options),/stdlib.cmi/);
    tar=safeTar;
    const installed=await v.installRelease(release,root,options);
    assert.equal(installed,path.join(root,'verifier/0.2.0'));
    await assert.rejects(v.installRelease(release,root,options),/already installed/);
    assert.deepEqual(await fs.readdir(path.join(root,'verifier')),['0.2.0']);
    assert.equal((await v.readManifest(path.join(installed,'bin/caravan'),installed)).version,'0.2.0');
  } finally {await new Promise(resolve=>server.close(resolve));await fs.rm(root,{recursive:true,force:true});}
});

test('malformed release inputs fail before filesystem or network activity',async()=>{
  await assert.rejects(v.installRelease(null,'/unused'),/Invalid release/);
  await assert.rejects(v.installRelease({tag:'v0.2.0',manifest,assets:{}},'/unused'),/Invalid release/);
  await assert.rejects(v.fetchRelease('../bad'),/Invalid version/);
});

test('release assets include native Windows x64 only',()=>{
  assert.equal(v.platformAsset('win32','x64'),'caravan-win32-x64.tar.gz');
  assert.equal(v.platformAsset('win32','arm64'),undefined);
  assert.equal(v.platformAsset('linux','x64'),'caravan-linux-x64.tar.gz');
  assert.equal(v.platformAsset('darwin','arm64'),'caravan-darwin-arm64.tar.gz');
});
test('Windows toolchain environment has one PATH and OCAMLLIB spelling',()=>{
  const base={Path:'C:\\Windows\\System32',pAtH:'ignored',OcamlLib:'wrong',SystemRoot:'C:\\Windows',OTHER:'kept'};
  const env=v.toolchainEnvironment('C:\\toolchain',base,'win32');
  assert.deepEqual(Object.keys(env).filter(k=>k.toUpperCase()==='PATH'),['PATH']);
  assert.deepEqual(Object.keys(env).filter(k=>k.toUpperCase()==='OCAMLLIB'),['OCAMLLIB']);
  assert.equal(env.PATH,'C:\\toolchain\\bin;C:\\Windows\\System32');
  assert.equal(env.OCAMLLIB,'C:\\toolchain\\lib\\ocaml');
  assert.equal(env.SystemRoot,base.SystemRoot);
  assert.equal(env.OTHER,'kept');
  assert.equal(base.OcamlLib,'wrong');
  const duplicate=v.toolchainEnvironment('C:\\toolchain',{Path:'old',PATH:'canonical'},'win32');
  assert.equal(duplicate.PATH,'C:\\toolchain\\bin;canonical');
});
test('all platforms reject Windows archive drive, ADS and dot-component paths',async()=>{
  const manifestBytes=Buffer.from(JSON.stringify(manifest));
  let tar;
  const hash=b=>require('node:crypto').createHash('sha256').update(b).digest('hex');
  const asset='caravan-win32-x64.tar.gz';
  const server=http.createServer((req,res)=>{
    if(req.url==='/SHA256SUMS')res.end(`${hash(manifestBytes)}  manifest.json\n${hash(tar)}  ${asset}\n`);
    else res.end(req.url==='/manifest.json'?manifestBytes:tar);
  });
  await new Promise(resolve=>server.listen(0,'127.0.0.1',resolve));
  const root=await fs.mkdtemp(path.join(os.tmpdir(),'caravan-path-test-'));
  const base=`http://127.0.0.1:${server.address().port}`;
  const release={tag:'v0.2.0',manifest,assets:new Map(['SHA256SUMS','manifest.json',asset].map(n=>[n,`${base}/${n}`]))};
  try {
    for(const name of ['C:/escape','C:escape','bin/caravan.exe:stream','bin/../escape','bin/./caravan.exe','bin/caravan.exe.','bin\\caravan.exe']) {
      tar=archive([[name,'unsafe']]);
      await assert.rejects(v.installRelease(release,root,{asset,allowHttpForTests:true}),/Unsafe/);
    }
    assert.deepEqual(await fs.readdir(path.join(root,'verifier')),[]);
  } finally {
    await new Promise(resolve=>server.close(resolve));
    await fs.rm(root,{recursive:true,force:true});
  }
});

test('minimal native test PATH preserves Windows system tools',()=>{
  assert.equal(systemPath({sYsTeMrOoT:'C:\\Windows'},'win32'),'C:\\Windows\\System32;C:\\Windows');
  assert.equal(systemPath({},'linux'),'/usr/bin:/bin');
  assert.throws(()=>systemPath({},'win32'),/SystemRoot/);
});
