import { createServer } from 'http';
import { existsSync, readFileSync, statSync } from 'fs';
import { extname, join, normalize } from 'path';
import { WebSocketServer, WebSocket } from 'ws';
import { randomBytes } from 'crypto';

type Card={s:string,r:string,id:string}; type P={name:string,score:number,hand:Card[]}; type Room={code:string,winning:number,clients:(WebSocket|null)[],state:any};
const rooms=new Map<string,Room>(); const suits=['♠','♥','♦','♣'],ranks=['2','3','4','5','6','7','8','9','10','J','Q','K','A'];const values:any=Object.fromEntries(ranks.map((r,i)=>[r,i+2]));const pts:any={'Two Pair':5,'Three of a Kind':10,'Straight':15,'Flush':20,'Full House':25,'Four of a Kind':50,'Straight Flush':75,'Royal Flush':100};
function deck(){const d:Card[]=[];for(const s of suits)for(const r of ranks)d.push({s,r,id:randomBytes(5).toString('hex')});for(let i=d.length-1;i;i--){const j=Math.floor(Math.random()*(i+1));[d[i],d[j]]=[d[j],d[i]]}return d} function classify(cs:Card[]){if(cs.length<2||cs.length>5)return null;const ns=cs.map(c=>values[c.r]).sort((a,b)=>a-b),cnt:any={};cs.forEach(c=>cnt[c.r]=(cnt[c.r]||0)+1);const vals=Object.values(cnt).sort((a:any,b:any)=>b-a),flush=cs.length===5&&cs.every(c=>c.s===cs[0].s),u=[...new Set(ns)];const straight=u.length===5&&((u[4] as number)-(u[0] as number)===4||u.join(',')==='2,3,4,5,14');if(cs.length===5&&flush&&straight)return (Math.max(...u as number[])===14?'Royal Flush':'Straight Flush');if(vals[0]===4)return'Four of a Kind';if(vals[0]===3&&vals[1]===2)return'Full House';if(flush)return'Flush';if(straight)return'Straight';if(vals[0]===3)return'Three of a Kind';if(vals[0]===2&&vals[1]===2)return'Two Pair';return null}
function init(winning:number){let d=deck();const nodes=[d.pop()!,d.pop()!,d.pop()!,d.pop()!];const ps=[0,1].map(i=>({name:`Player ${i+1}`,score:0,hand:[] as Card[]}));ps.forEach(p=>{for(let i=0;i<6;i++)p.hand.push(d.pop()!)});return{game:'Node Attack',winning,players:ps,current:0,nodes,deck:d,used:[],round:1,over:false,winner:null,log:['Node Attack started.'],combo:[0,0]}}
function publicState(s:any){return{game:s.game,winning:s.winning,players:s.players.map((p:P)=>({name:p.name,score:p.score,hand:p.hand})),current:s.current,nodes:s.nodes,deckCount:s.deck.length,usedCount:s.used.length,round:s.round,over:s.over,winner:s.winner,log:s.log.slice(0,30)}}
function refill(s:any,p:number){while(s.players[p].hand.length<6){if(!s.deck.length){if(!s.used.length)break;s.deck=s.used.splice(0);for(let i=s.deck.length-1;i;i--){const j=Math.floor(Math.random()*(i+1));[s.deck[i],s.deck[j]]=[s.deck[j],s.deck[i]]}}s.players[p].hand.push(s.deck.pop())}}
function broadcast(r:Room){const msg=JSON.stringify({type:'state',state:publicState(r.state)});r.clients.forEach(c=>c?.send(msg))}
function err(c:WebSocket,m:string){c.send(JSON.stringify({type:'error',message:m}))}
function action(r:Room,pi:number,a:any){
  const s=r.state;
  if(a.kind==='rematch'&&s.over){r.state=init(r.winning);broadcast(r);return}
  if(s.over||s.current!==pi)return;
  const p=s.players[pi];
  if(a.kind==='finish'){
    refill(s,pi);s.combo[pi]=0;s.current=1-pi;
    s.log.unshift(`${p.name} finished the turn.`);broadcast(r);return;
  }
  if(a.kind==='discard'){
    const raw:Array<unknown>=Array.isArray(a.indices)?a.indices:[];
    const inds:number[]=[...new Set(raw.filter((i):i is number=>Number.isInteger(i)&&i>=0&&i<p.hand.length))];
    if(!inds.length||inds.length>4)return err(r.clients[pi]!, 'Select 1–4 cards.');
    const cards=p.hand.filter((_:Card,i:number)=>inds.includes(i));
    p.hand=p.hand.filter((_:Card,i:number)=>!inds.includes(i));
    s.used.push(...cards);refill(s,pi);s.combo[pi]=0;s.current=1-pi;
    s.log.unshift(`${p.name} discarded ${cards.length} card(s).`);broadcast(r);return;
  }
  if(a.kind==='play'){
    const ni=a.node;
    const raw:Array<unknown>=Array.isArray(a.indices)?a.indices:[];
    const inds:number[]=[...new Set(raw.filter((i):i is number=>Number.isInteger(i)&&i>=0&&i<p.hand.length))];
    if(!Number.isInteger(ni)||!s.nodes[ni]||!inds.length||inds.length>4)return err(r.clients[pi]!, 'Invalid selection.');
    const cards:Card[]=[s.nodes[ni] as Card,...inds.map(i=>p.hand[i])];
    const type=classify(cards);
    if(!type)return err(r.clients[pi]!, 'Selected cards do not form a scoring hand.');
    const withoutNode=classify(cards.slice(1));
    if(withoutNode===type)return err(r.clients[pi]!, 'The node card must be part of the scoring hand.');
    const base=pts[type];
    const combo=s.combo[pi]||0;
    const mult=[1,1.5,2,3][combo]||3;
    const gained=base*mult;
    p.score+=gained;s.combo[pi]++;
    s.used.push(...cards);p.hand=p.hand.filter((_:Card,i:number)=>!inds.includes(i));s.nodes[ni]=null;
    s.log.unshift(`${p.name} played ${type} for ${gained} points.`);
    if(p.score>=s.winning){s.over=true;s.winner=pi;s.log.unshift(`${p.name} wins!`);broadcast(r);return}
    if(s.nodes.every((x:Card|null)=>!x)){
      s.nodes=[s.deck.pop()!,s.deck.pop()!,s.deck.pop()!,s.deck.pop()!];
      s.round++;s.current=1-pi;s.players.forEach((_:P,i:number)=>{s.combo[i]=0;refill(s,i)});
      s.log.unshift(`Round ${s.round} started.`);
    }
    broadcast(r);
  }
}
const port=Number(process.env.PORT)||8080;
const root=process.cwd();
const dist=join(root,'dist');
const mime:Record<string,string>={'.html':'text/html; charset=utf-8','.js':'text/javascript; charset=utf-8','.css':'text/css; charset=utf-8','.json':'application/json; charset=utf-8','.svg':'image/svg+xml','.png':'image/png','.jpg':'image/jpeg','.jpeg':'image/jpeg','.ico':'image/x-icon'};
const httpServer=createServer((req,res)=>{
  const url=new URL(req.url||'/',`http://${req.headers.host||'localhost'}`);
  if(url.pathname==='/health'){res.writeHead(200,{'Content-Type':'text/plain'});res.end('ok');return;}
  let pathname=decodeURIComponent(url.pathname);
  if(pathname==='/') pathname='/index.html';
  const candidate=join(dist,normalize(pathname));
  let file=candidate;
  if(!existsSync(file)||!statSync(file).isFile()) file=join(dist,'index.html');
  if(!existsSync(file)){res.writeHead(503);res.end('Build not found');return;}
  res.writeHead(200,{'Content-Type':mime[extname(file)]||'application/octet-stream'});res.end(readFileSync(file));
});
const wss=new WebSocketServer({server:httpServer});wss.on('connection',c=>{c.on('message',raw=>{let m:any;try{m=JSON.parse(raw.toString())}catch{return}if(m.type==='create'||m.type==='join'){let code=(m.room||'').toUpperCase();if(m.type==='create'){do code=randomBytes(3).toString('hex').toUpperCase();while(rooms.has(code));rooms.set(code,{code,winning:m.winning||150,clients:[null,null],state:init(m.winning||150)})}const r=rooms.get(code);if(!r)return err(c,'Room not found.');const pi=r.clients[0]?1:0;if(r.clients[pi])return err(c,'Room is full.');r.clients[pi]=c;(c as any).room=code;(c as any).player=pi;c.send(JSON.stringify({type:'welcome',room:code,player:pi,state:publicState(r.state)}));broadcast(r)}else if(m.type==='action'){const r=rooms.get(m.room);if(r)action(r,(c as any).player,m.action)}});c.on('close',()=>{const code=(c as any).room;if(code&&rooms.has(code)){const r=rooms.get(code)!;r.clients[(c as any).player]=null;r.state.log.unshift(`Player ${(c as any).player+1} disconnected.`);broadcast(r)}})});httpServer.listen(port,'0.0.0.0',()=>console.log(`Node Attack server listening on http://0.0.0.0:${port}`));
