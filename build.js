// build : src/shell.html + src/app.js -> index.html (JS sans commentaires, // protégés)
const fs=require('fs'),cp=require('child_process'),path=require('path');
const d=__dirname,shell=fs.readFileSync(path.join(d,'src','shell.html'),'utf8');
const r=cp.spawnSync('npx',['-y','esbuild','--minify-whitespace','--charset=utf8','--log-level=warning'],{input:Buffer.concat(['thumbs.js','app.js','extra.js','cloud.js'].map(f=>fs.readFileSync(path.join(d,'src',f)))),shell:true,maxBuffer:1<<28});
if(r.status!==0){console.error(String(r.stderr));process.exit(1)}
let js=String(r.stdout).replace(/:\/\//g,':\\/\\/');
if(/\/\*/.test(js))console.warn('ATTENTION : séquence /* restante dans le JS');
fs.writeFileSync(path.join(d,'index.html'),shell+js+'\n</script>\n</body></html>\n');
fs.writeFileSync(path.join(d,'.chk.js'),js);
cp.execSync('node --check .chk.js',{cwd:d,stdio:'inherit'});fs.unlinkSync(path.join(d,'.chk.js'));
console.log('index.html',(fs.statSync(path.join(d,'index.html')).size/1024|0)+' Ko');
