#!/usr/bin/env python3
"""Launch only private work with a memory gate and durable command/timing receipt."""
import argparse,json,pathlib,subprocess,time,resource

def memory_used():
    m={k:int(v.split()[0])*1024 for k,v in (x.split(':',1) for x in pathlib.Path('/proc/meminfo').read_text().splitlines())}
    return m['MemTotal']-m['MemAvailable']

def main():
    p=argparse.ArgumentParser();p.add_argument('--log',type=pathlib.Path,required=True);p.add_argument('command',nargs=argparse.REMAINDER);a=p.parse_args()
    cmd=a.command[1:] if a.command[:1]==['--'] else a.command
    used=memory_used()
    if used>2*1024**4:raise SystemExit('Memory launch ceiling exceeded')
    a.log.parent.mkdir(parents=True,exist_ok=True);start=time.monotonic()
    with a.log.open('w') as f:r=subprocess.run(cmd,stdout=f,stderr=subprocess.STDOUT)
    receipt=dict(command=cmd,cwd=str(pathlib.Path.cwd()),returncode=r.returncode,elapsed_seconds=time.monotonic()-start,memory_used_at_start=used,max_child_rss_kib=resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
    a.log.with_suffix('.receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));raise SystemExit(r.returncode)
if __name__=='__main__':main()
