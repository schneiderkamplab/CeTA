from pathlib import Path
import time,json,gzip,hashlib,subprocess
R=Path.cwd();O=R/'target/certificate-performance-20261027';B=R/'target/unified-certificate-performance-20261027/ceta';S=R/'target/shared-frontier-20261027';old=R/'target/unified-usable-membership-20261026/ceta'
def run(cmd,name):
 with (O/name).open('w') as f:subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT,check=True)
while not (B.parent/'build.json').exists():time.sleep(5)
run(['python3','tests/unified/check_dispatch.py',str(B)],'dispatch.json')
run(['python3','tests/unified/check_parser_differential.py','--before',str(old),'--after',str(B),'--output',str(O/'parser-differential.json')],'parser-differential.log')
run(['python3','tests/unified/check_negatives.py',str(B),'--output',str(O/'negatives.json.gz')],'negatives.log')
while not (S/'reexport.json.gz').exists():time.sleep(5)
manifest=json.loads(gzip.decompress((S/'manifest.json.gz').read_bytes()));rows={r['root']:r for r in manifest['roots']};meta=json.loads((R/'target/compact-frontier-20261026/provenance.json').read_text())
meta['archive_sha256']=manifest['artifact_archive_sha256'];meta['manifest_sha256']=hashlib.sha256((S/'manifest.json.gz').read_bytes()).hexdigest()
meta['jobs']=[dict(r,proof_sha256=rows[r['root']]['proof_sha256'],compact_proof_sha256=r['proof_sha256']) for r in meta['jobs']]
(S/'provenance.json').write_text(json.dumps(meta,indent=2)+'\n')
run(['python3','tests/unified/check_frontier.py','--binary',str(B),'--provenance',str(S/'provenance.json'),'--baseline-results',str(R.parent/'CeTA-Lean/target/production-certification-benchmark-20261025/ceta.json.gz'),'--archive',str(S/'frontier-5412-shared.zip'),'--output',str(O/'frontier.json.gz'),'--workers','32','--child-spec','tests/unified/shared-children.json'],'frontier.log')
print('VALIDATED',flush=True)
