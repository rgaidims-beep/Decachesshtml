/* ============================================================
   DECACHESS — Game Logic + AI + Online Multiplayer + Themes
   PeerJS WebRTC peer-to-peer · 10 themes · 10 boards · 10 skins
   ============================================================ */
'use strict';

// ── Piece constants ───────────────────────────────────────────
const KING=1,QUEEN=2,ROOK=3,KNIGHT=4,PAWN=5;
const WIZARD=6,DRAGON=7,CHAMPION=8,ARCHER=9,PORTAL=10;
const WHITE='w',BLACK='b';

const GLYPHS={
  w:{[KING]:'♔',[QUEEN]:'♕',[ROOK]:'♖',[KNIGHT]:'♘',[PAWN]:'♙',[WIZARD]:'🧙',[DRAGON]:'🐉',[CHAMPION]:'🛡',[ARCHER]:'🏹',[PORTAL]:'🌀'},
  b:{[KING]:'♚',[QUEEN]:'♛',[ROOK]:'♜',[KNIGHT]:'♞',[PAWN]:'♟',[WIZARD]:'🧙',[DRAGON]:'🐉',[CHAMPION]:'🛡',[ARCHER]:'🏹',[PORTAL]:'🌀'}
};
const GLYPH_EMOJI=new Set([WIZARD,DRAGON,CHAMPION,ARCHER,PORTAL]);
const PIECE_NAMES={[KING]:'King',[QUEEN]:'Queen',[ROOK]:'Rook',[KNIGHT]:'Knight',[PAWN]:'Pawn',[WIZARD]:'Wizard',[DRAGON]:'Dragon',[CHAMPION]:'Champion',[ARCHER]:'Archer',[PORTAL]:'Portal'};
const PIECE_LETTERS={[KING]:'K',[QUEEN]:'Q',[ROOK]:'R',[KNIGHT]:'N',[PAWN]:'',[WIZARD]:'W',[DRAGON]:'D',[CHAMPION]:'C',[ARCHER]:'A',[PORTAL]:'O'};
const PIECE_VALUE={[KING]:20000,[QUEEN]:950,[ROOK]:500,[KNIGHT]:320,[PAWN]:100,[WIZARD]:750,[DRAGON]:480,[CHAMPION]:400,[ARCHER]:350,[PORTAL]:300};

// ── Board helpers ─────────────────────────────────────────────
const SIZE=10;
const inBounds=(r,c)=>r>=0&&r<SIZE&&c>=0&&c<SIZE;
const makePiece=(type,color)=>({type,color,hasMoved:false,tripleUsed:false});
const cloneBoard=b=>b.map(row=>row.map(p=>p?{...p}:null));
function emptyBoard(){return Array.from({length:SIZE},()=>new Array(SIZE).fill(null));}

function buildStartingBoard(){
  const board=emptyBoard();
  const back=[ROOK,KNIGHT,WIZARD,QUEEN,KING,CHAMPION,WIZARD,KNIGHT,ROOK,DRAGON];
  back.forEach((t,c)=>{board[0][c]=makePiece(t,BLACK);});
  for(let c=0;c<SIZE;c++) board[1][c]=makePiece(PAWN,BLACK);
  board[2][2]=makePiece(ARCHER,BLACK);board[2][4]=makePiece(PAWN,BLACK);
  board[2][5]=makePiece(PORTAL,BLACK);board[2][7]=makePiece(ARCHER,BLACK);
  board[7][2]=makePiece(ARCHER,WHITE);board[7][4]=makePiece(PAWN,WHITE);
  board[7][5]=makePiece(PORTAL,WHITE);board[7][7]=makePiece(ARCHER,WHITE);
  for(let c=0;c<SIZE;c++) board[8][c]=makePiece(PAWN,WHITE);
  back.forEach((t,c)=>{board[9][c]=makePiece(t,WHITE);});
  return board;
}

// ── Game State ────────────────────────────────────────────────
let state={};
function initState(){
  state={
    board:buildStartingBoard(),turn:WHITE,selected:null,legalMoves:[],
    moveLog:[],capturedByWhite:[],capturedByBlack:[],
    flipped:false,enPassantTarget:null,inCheck:false,
    gameOver:false,pendingPromotion:null,lastMove:null,
    aiColor:null,aiLevel:3,aiThinking:false,
    mpMode:false,mpColor:null,mpConnected:false,
  };
}

// ── Move Generation ───────────────────────────────────────────
function getRawMoves(board,r,c,ep){
  const piece=board[r][c]; if(!piece) return [];
  const {type,color}=piece; const moves=[]; const enemy=color===WHITE?BLACK:WHITE;
  const addSlide=(dr,dc,max)=>{
    for(let i=1;i<=max;i++){
      const nr=r+dr*i,nc=c+dc*i; if(!inBounds(nr,nc)) break;
      if(board[nr][nc]){if(board[nr][nc].color===enemy) moves.push({row:nr,col:nc,special:null}); break;}
      moves.push({row:nr,col:nc,special:null});
    }
  };
  switch(type){
    case KING:
      [[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]].forEach(([dr,dc])=>{
        const nr=r+dr,nc=c+dc; if(!inBounds(nr,nc)) return;
        if(!board[nr][nc]||board[nr][nc].color===enemy) moves.push({row:nr,col:nc,special:null});
      });
      if(!piece.hasMoved){
        const hr=color===WHITE?9:0;
        if(r===hr){
          for(let d=c+1;d<SIZE;d++){const p=board[r][d];if(p&&p.color===color&&(p.type===ROOK||p.type===DRAGON)&&!p.hasMoved){let ok=true;for(let cc=c+1;cc<d;cc++)if(board[r][cc]){ok=false;break;}if(ok)moves.push({row:r,col:c+2,special:'castleK'});break;}if(p)break;}
          for(let d=c-1;d>=0;d--){const p=board[r][d];if(p&&p.color===color&&(p.type===ROOK||p.type===DRAGON)&&!p.hasMoved){let ok=true;for(let cc=d+1;cc<c;cc++)if(board[r][cc]){ok=false;break;}if(ok)moves.push({row:r,col:c-2,special:'castleQ'});break;}if(p)break;}
        }
      } break;
    case QUEEN: [[-1,0],[1,0],[0,-1],[0,1],[-1,-1],[-1,1],[1,-1],[1,1]].forEach(([dr,dc])=>addSlide(dr,dc,10)); break;
    case ROOK:  [[-1,0],[1,0],[0,-1],[0,1]].forEach(([dr,dc])=>addSlide(dr,dc,10)); break;
    case KNIGHT:
      [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]].forEach(([dr,dc])=>{
        const nr=r+dr,nc=c+dc; if(!inBounds(nr,nc)) return;
        if(!board[nr][nc]||board[nr][nc].color===enemy) moves.push({row:nr,col:nc,special:null});
      }); break;
    case PAWN:{
      const dir=color===WHITE?-1:1,promoRow=color===WHITE?0:9,nr=r+dir;
      if(inBounds(nr,c)&&!board[nr][c]){
        moves.push({row:nr,col:c,special:nr===promoRow?'promotion':null});
        if(!piece.hasMoved){
          const nr2=r+2*dir;
          if(inBounds(nr2,c)&&!board[nr2][c]){
            moves.push({row:nr2,col:c,special:'double_push'});
            if(!piece.tripleUsed){const nr3=r+3*dir;if(inBounds(nr3,c)&&!board[nr3][c])moves.push({row:nr3,col:c,special:'triple_push'});}
          }
        }
      }
      [-1,1].forEach(dc=>{
        const nc=c+dc; if(!inBounds(nr,nc)) return;
        if(board[nr][nc]?.color===enemy) moves.push({row:nr,col:nc,special:nr===promoRow?'promotion':null});
        if(ep&&ep[0]===nr&&ep[1]===nc) moves.push({row:nr,col:nc,special:'ep'});
      }); break;
    }
    case WIZARD:
      [[-1,-1],[-1,1],[1,-1],[1,1]].forEach(([dr,dc])=>addSlide(dr,dc,10));
      [[-2,-1],[-2,1],[-1,-2],[-1,2],[1,-2],[1,2],[2,-1],[2,1]].forEach(([dr,dc])=>{
        const nr=r+dr,nc=c+dc; if(!inBounds(nr,nc)) return;
        if(!board[nr][nc]||board[nr][nc].color===enemy) moves.push({row:nr,col:nc,special:null});
      }); break;
    case DRAGON: [[-1,0],[1,0],[0,-1],[0,1]].forEach(([dr,dc])=>addSlide(dr,dc,4)); break;
    case CHAMPION:
      [[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]].forEach(([dr,dc])=>{
        const nr1=r+dr,nc1=c+dc; if(!inBounds(nr1,nc1)) return;
        if(!board[nr1][nc1]){
          moves.push({row:nr1,col:nc1,special:null});
          const nr2=r+dr*2,nc2=c+dc*2;
          if(inBounds(nr2,nc2)&&(!board[nr2][nc2]||board[nr2][nc2].color===enemy)) moves.push({row:nr2,col:nc2,special:null});
        } else if(board[nr1][nc1].color===enemy) moves.push({row:nr1,col:nc1,special:null});
      }); break;
    case ARCHER:
      [[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]].forEach(([dr,dc])=>{
        const nr=r+dr,nc=c+dc; if(!inBounds(nr,nc)) return;
        if(!board[nr][nc]) moves.push({row:nr,col:nc,special:null});
      });
      [[-1,0],[1,0],[0,-1],[0,1]].forEach(([dr,dc])=>{
        const nr1=r+dr,nc1=c+dc;
        if(inBounds(nr1,nc1)&&board[nr1][nc1]?.color===enemy) moves.push({row:nr1,col:nc1,special:'archer_ranged'});
        const nr2=r+dr*2,nc2=c+dc*2;
        if(inBounds(nr2,nc2)&&board[nr2][nc2]?.color===enemy) moves.push({row:nr2,col:nc2,special:'archer_ranged'});
      }); break;
    case PORTAL:
      [[-1,-1],[-1,0],[-1,1],[0,-1],[0,1],[1,-1],[1,0],[1,1]].forEach(([dr,dc])=>{
        const nr=r+dr,nc=c+dc; if(!inBounds(nr,nc)) return;
        if(!board[nr][nc]||board[nr][nc].color===enemy) moves.push({row:nr,col:nc,special:null});
      });
      for(let tr=0;tr<SIZE;tr++)for(let tc=0;tc<SIZE;tc++){
        if(tr===r&&tc===c) continue;
        if(Math.max(Math.abs(tr-r),Math.abs(tc-c))>3) continue;
        const t=board[tr][tc];
        if(t&&t.color===color&&t.type!==KING) moves.push({row:tr,col:tc,special:'portal_swap'});
      } break;
  }
  return moves;
}

// ── Check detection ───────────────────────────────────────────
function findKing(board,color){
  for(let r=0;r<SIZE;r++)for(let c=0;c<SIZE;c++)if(board[r][c]?.type===KING&&board[r][c]?.color===color)return[r,c];
  return null;
}
function isInCheck(board,color,ep){
  const king=findKing(board,color); if(!king) return false;
  const enemy=color===WHITE?BLACK:WHITE;
  for(let sr=0;sr<SIZE;sr++)for(let sc=0;sc<SIZE;sc++){
    const p=board[sr][sc]; if(!p||p.color!==enemy) continue;
    if(getRawMoves(board,sr,sc,ep).some(m=>m.row===king[0]&&m.col===king[1])) return true;
  }
  return false;
}

// ── Apply move ────────────────────────────────────────────────
function applyMove(board,fromR,fromC,toR,toC,special,ep){
  const nb=cloneBoard(board); const piece=nb[fromR][fromC];
  if(special==='portal_swap'){const tmp=nb[toR][toC];nb[toR][toC]=piece;nb[fromR][fromC]=tmp;return nb;}
  if(special==='archer_ranged'){nb[toR][toC]=null;return nb;}
  if(special==='ep') nb[toR+(piece.color===WHITE?1:-1)][toC]=null;
  if(special==='castleK'||special==='castleQ'){
    const rc=special==='castleK'
      ?(()=>{for(let d=fromC+1;d<SIZE;d++){if(nb[fromR][d]&&(nb[fromR][d].type===ROOK||nb[fromR][d].type===DRAGON))return d;}})()
      :(()=>{for(let d=fromC-1;d>=0;d--){if(nb[fromR][d]&&(nb[fromR][d].type===ROOK||nb[fromR][d].type===DRAGON))return d;}})();
    const rd=special==='castleK'?toC-1:toC+1;
    nb[fromR][rd]=nb[fromR][rc];nb[fromR][rd].hasMoved=true;nb[fromR][rc]=null;
  }
  if(special==='triple_push') piece.tripleUsed=true;
  nb[toR][toC]=piece;nb[fromR][fromC]=null;piece.hasMoved=true;
  return nb;
}

// ── Legal moves ───────────────────────────────────────────────
function getLegalMoves(board,r,c,ep){
  const piece=board[r][c]; if(!piece) return [];
  return getRawMoves(board,r,c,ep).filter(m=>{
    const nb=applyMove(board,r,c,m.row,m.col,m.special,ep);
    return !isInCheck(nb,piece.color,null);
  });
}
function hasAnyLegal(board,color,ep){
  for(let r=0;r<SIZE;r++)for(let c=0;c<SIZE;c++)if(board[r][c]?.color===color&&getLegalMoves(board,r,c,ep).length>0)return true;
  return false;
}
function getAllLegal(board,color,ep){
  const all=[];
  for(let r=0;r<SIZE;r++)for(let c=0;c<SIZE;c++)
    if(board[r][c]?.color===color) getLegalMoves(board,r,c,ep).forEach(m=>all.push({fromR:r,fromC:c,...m}));
  return all;
}

// ── Evaluation & AI ───────────────────────────────────────────
const CENTER_BONUS=(()=>{const b=[];for(let r=0;r<SIZE;r++){b.push([]);for(let c=0;c<SIZE;c++){const dr=Math.abs(r-4.5),dc=Math.abs(c-4.5);b[r].push(Math.round((5-dr)*(5-dc)*.8));}}return b;})();
function evaluate(board){
  let s=0;
  for(let r=0;r<SIZE;r++)for(let c=0;c<SIZE;c++){
    const p=board[r][c];if(!p)continue;
    const v=PIECE_VALUE[p.type]+CENTER_BONUS[r][c];
    s+=p.color===WHITE?v:-v;
  }
  return s;
}
function minimax(board,depth,alpha,beta,max,ep){
  if(depth===0) return evaluate(board);
  const color=max?WHITE:BLACK;
  const moves=getAllLegal(board,color,ep);
  if(!moves.length) return isInCheck(board,color,ep)?(max?-100000:100000):0;
  moves.sort((a,b)=>{const va=board[a.row][a.col]?PIECE_VALUE[board[a.row][a.col].type]:0,vb=board[b.row][b.col]?PIECE_VALUE[board[b.row][b.col].type]:0;return vb-va;});
  if(max){let best=-Infinity;for(const m of moves){const nb=applyMove(board,m.fromR,m.fromC,m.row,m.col,m.special,ep);best=Math.max(best,minimax(nb,depth-1,alpha,beta,false,m.special==='double_push'?[m.fromR+1,m.fromC]:null));alpha=Math.max(alpha,best);if(beta<=alpha)break;}return best;}
  else{let best=Infinity;for(const m of moves){const nb=applyMove(board,m.fromR,m.fromC,m.row,m.col,m.special,ep);best=Math.min(best,minimax(nb,depth-1,alpha,beta,true,m.special==='double_push'?[m.fromR-1,m.fromC]:null));beta=Math.min(beta,best);if(beta<=alpha)break;}return best;}
}
const AI_CFG={1:{depth:1,noise:450,blunder:.40},2:{depth:1,noise:160,blunder:.15},3:{depth:2,noise:55,blunder:0},4:{depth:3,noise:12,blunder:0},5:{depth:4,noise:0,blunder:0}};
function pickAI(board,color,ep,level){
  const cfg=AI_CFG[level]||AI_CFG[3];
  const moves=getAllLegal(board,color,ep); if(!moves.length) return null;
  if(cfg.blunder>0&&Math.random()<cfg.blunder) return moves[Math.floor(Math.random()*moves.length)];
  const max=color===WHITE; let bestScore=max?-Infinity:Infinity,bestMoves=[];
  for(const m of moves){
    const nb=applyMove(board,m.fromR,m.fromC,m.row,m.col,m.special,ep);
    let score=minimax(nb,cfg.depth-1,-Infinity,Infinity,!max,m.special==='double_push'?[m.fromR+(color===WHITE?-1:1),m.fromC]:null);
    score+=(Math.random()-.5)*cfg.noise;
    if(max?score>bestScore:score<bestScore){bestScore=score;bestMoves=[m];}
    else if(Math.abs(score-bestScore)<1) bestMoves.push(m);
  }
  return bestMoves[Math.floor(Math.random()*bestMoves.length)];
}
function maybeRunAI(){
  if(!state.aiColor||state.turn!==state.aiColor||state.gameOver||state.pendingPromotion||state.aiThinking) return;
  state.aiThinking=true;
  const bar=document.getElementById('status-bar');
  bar.textContent='🤖 AI is thinking…';bar.classList.remove('check');
  const {board,enPassantTarget,aiLevel,aiColor}=state;
  setTimeout(()=>{
    const move=pickAI(board,aiColor,enPassantTarget,aiLevel);
    state.aiThinking=false;
    if(!move||state.gameOver){renderAll();return;}
    executeMove(move.fromR,move.fromC,move.row,move.col,move.special,true);
  },80);
}

// ══════════════════════════════════════════════════════════════
//  MULTIPLAYER — PeerJS WebRTC
// ══════════════════════════════════════════════════════════════
let peer=null,mpConn=null,mpIsHost=false,mpRoomCode='';

function genRoomCode(){return Math.random().toString(36).substring(2,8).toUpperCase();}

function initPeer(id){
  return new Promise((resolve,reject)=>{
    if(peer){try{peer.destroy();}catch(e){} peer=null;}
    peer=new Peer(id,{debug:0});
    peer.on('open',resolve);
    peer.on('error',reject);
  });
}

document.getElementById('btn-create-room').addEventListener('click',async()=>{
  const btn=document.getElementById('btn-create-room');
  btn.disabled=true;btn.textContent='Connecting…';
  mpRoomCode=genRoomCode();
  try{
    await initPeer('deca-'+mpRoomCode);
    document.getElementById('room-code-text').textContent=mpRoomCode;
    document.getElementById('room-created').style.display='block';
    btn.style.display='none';
    mpIsHost=true;
    peer.on('connection',conn=>{
      mpConn=conn;
      setupConn(conn);
      conn.on('open',()=>{
        document.getElementById('mp-lobby').style.display='none';
        document.getElementById('mp-connected').style.display='block';
        document.getElementById('mp-you-are').textContent='You are playing as White ♔';
        document.getElementById('btn-start-mp').style.display='block';
      });
    });
  }catch(e){btn.disabled=false;btn.textContent='Generate Room Code';showJoinStatus('Connection failed. Try again.','err');}
});

document.getElementById('btn-join-room').addEventListener('click',async()=>{
  const code=document.getElementById('join-code-input').value.trim().toUpperCase();
  if(code.length<4){showJoinStatus('Enter a valid room code.','err');return;}
  const btn=document.getElementById('btn-join-room');
  btn.disabled=true;btn.textContent='Joining…';
  showJoinStatus('Connecting…','');
  try{
    await initPeer('deca-joiner-'+Date.now());
    const conn=peer.connect('deca-'+code,{reliable:true});
    mpConn=conn; mpIsHost=false; mpRoomCode=code;
    setupConn(conn);
    conn.on('open',()=>{
      showJoinStatus('Connected!','ok');
      document.getElementById('mp-lobby').style.display='none';
      document.getElementById('mp-connected').style.display='block';
      document.getElementById('mp-you-are').textContent='You are playing as Black ♚';
      document.getElementById('btn-start-mp').style.display='none';
      // joiner waits for host to start
    });
    conn.on('error',()=>{showJoinStatus('Could not connect. Check the code.','err');btn.disabled=false;btn.textContent='Join';});
    setTimeout(()=>{if(!state.mpConnected){showJoinStatus('Timed out. Check the code.','err');btn.disabled=false;btn.textContent='Join';}},8000);
  }catch(e){showJoinStatus('Connection error.','err');btn.disabled=false;btn.textContent='Join';}
});

document.getElementById('btn-start-mp').addEventListener('click',()=>{
  if(!mpConn) return;
  startMPGame();
  mpConn.send({type:'game_start'});
  document.getElementById('mp-modal').classList.add('hidden');
});

function setupConn(conn){
  conn.on('data',onMPData);
  conn.on('close',()=>{
    showMPStatus('Opponent disconnected','#e07070');
    state.mpConnected=false;
  });
  conn.on('error',e=>console.warn('MP conn error',e));
}

function onMPData(data){
  switch(data.type){
    case 'game_start':
      startMPGame();
      document.getElementById('mp-modal').classList.add('hidden');
      break;
    case 'move':
      if(state.gameOver||state.mpConnected===false) return;
      receiveRemoteMove(data.fromR,data.fromC,data.toR,data.toC,data.special,data.promoType);
      break;
    case 'resign':
      endGame('resign',state.mpColor);
      break;
  }
}

function startMPGame(){
  initState();
  state.mpMode=true;
  state.mpConnected=true;
  state.mpColor=mpIsHost?WHITE:BLACK;
  state.flipped=!mpIsHost; // black sees board from their side
  const badge=document.getElementById('mp-badge');
  badge.textContent=`🌐 Online — You: ${mpIsHost?'White ♔':'Black ♚'}`;
  badge.style.display='inline-block';
  document.getElementById('ai-badge').style.display='none';
  document.getElementById('mp-info-bar').style.display='flex';
  document.getElementById('mp-room-display').textContent='Room: '+mpRoomCode;
  showMPStatus('Connected — '+( mpIsHost?'White':'Black'),'#70e880');
  renderAll();
}

function receiveRemoteMove(fromR,fromC,toR,toC,special,promoType){
  executeMove(fromR,fromC,toR,toC,special,true,promoType);
}

function sendMove(fromR,fromC,toR,toC,special,promoType){
  if(state.mpMode&&mpConn&&state.mpConnected){
    mpConn.send({type:'move',fromR,fromC,toR,toC,special,promoType:promoType||null});
  }
}

function showJoinStatus(msg,cls){
  const el=document.getElementById('join-status');
  el.textContent=msg; el.className='join-status '+(cls||'');
}
function showMPStatus(msg,color){
  const el=document.getElementById('mp-conn-status');
  el.textContent=msg; el.style.color=color||'';
}
function copyRoomCode(){
  navigator.clipboard?.writeText(mpRoomCode).catch(()=>{});
  const el=document.querySelector('.btn[onclick="copyRoomCode()"]');
  if(el){const orig=el.textContent;el.textContent='✅ Copied!';setTimeout(()=>el.textContent=orig,2000);}
}

// ── Online multiplayer mode btn ───────────────────────────────
document.querySelectorAll('.mode-btn').forEach(btn=>{
  btn.addEventListener('click',()=>{
    document.querySelectorAll('.mode-btn').forEach(b=>b.classList.remove('active'));
    btn.classList.add('active');
    const mode=btn.dataset.mode;
    document.getElementById('ai-level-row').style.display=mode==='ai'?'flex':'none';
    if(mode==='mp') document.getElementById('mp-modal').classList.remove('hidden');
  });
});

// ══════════════════════════════════════════════════════════════
//  THEMES & SKINS SYSTEM
// ══════════════════════════════════════════════════════════════
const SITE_THEMES=[
  {id:'theme-darkgold',  name:'Dark Gold',   bg:'#0e0c0a', accent:'#c8992a'},
  {id:'theme-midnight',  name:'Midnight',    bg:'#050810', accent:'#4a90d9'},
  {id:'theme-forest',    name:'Forest',      bg:'#060a06', accent:'#4a9a4a'},
  {id:'theme-blood',     name:'Blood Red',   bg:'#0a0505', accent:'#c83030'},
  {id:'theme-cyber',     name:'Cyberpunk',   bg:'#030008', accent:'#cc00ff'},
  {id:'theme-ivory',     name:'Ivory',       bg:'#f5f0e8', accent:'#8b6914'},
  {id:'theme-royal',     name:'Royal Purple',bg:'#080510', accent:'#9040d0'},
  {id:'theme-arctic',    name:'Arctic Ice',  bg:'#020810', accent:'#60c8e8'},
  {id:'theme-pixel',     name:'Retro Pixel', bg:'#000000', accent:'#ffcc00'},
  {id:'theme-rosegold',  name:'Rose Gold',   bg:'#0f080c', accent:'#d4808a'},
];
const BOARD_SKINS=[
  {id:'board-classic',  name:'Classic Wood', a:'#d4b896',b:'#7a5230'},
  {id:'board-marble',   name:'Marble',       a:'#e8e0d8',b:'#7a7878'},
  {id:'board-obsidian', name:'Obsidian',     a:'#3a3a4a',b:'#18181f'},
  {id:'board-forest',   name:'Forest Moss',  a:'#b8c8a0',b:'#4a6030'},
  {id:'board-ocean',    name:'Ocean',        a:'#a0c8e0',b:'#1a5878'},
  {id:'board-lava',     name:'Lava',         a:'#e0a870',b:'#7a2808'},
  {id:'board-ice',      name:'Ice Crystal',  a:'#d8f0ff',b:'#5898c0'},
  {id:'board-sand',     name:'Desert Sand',  a:'#f0e0a0',b:'#c0980a'},
  {id:'board-void',     name:'Void',         a:'#1a0a30',b:'#08001a'},
  {id:'board-coral',    name:'Coral Reef',   a:'#f8c8b0',b:'#c85840'},
];
const PIECE_SKINS=[
  {id:'skin-classic',    name:'Classic',      preview:'♛'},
  {id:'skin-outlined',   name:'Outlined',     preview:'♛'},
  {id:'skin-neon',       name:'Neon Glow',    preview:'♛'},
  {id:'skin-goldsilver', name:'Gold & Silver',preview:'♛'},
  {id:'skin-fireice',    name:'Fire & Ice',   preview:'♛'},
  {id:'skin-pastel',     name:'Pastel',       preview:'♛'},
  {id:'skin-contrast',   name:'High Contrast',preview:'♛'},
  {id:'skin-vintage',    name:'Vintage',      preview:'♛'},
  {id:'skin-plasma',     name:'Plasma',       preview:'♛'},
  {id:'skin-shadow',     name:'Shadow',       preview:'♛'},
];

let currentSiteTheme='theme-darkgold';
let currentBoardSkin='board-classic';
let currentPieceSkin='skin-classic';

function loadSavedPrefs(){
  const st=localStorage.getItem('dc-site-theme');
  const bs=localStorage.getItem('dc-board-skin');
  const ps=localStorage.getItem('dc-piece-skin');
  if(st) applySiteTheme(st,false);
  if(bs) applyBoardSkin(bs,false);
  if(ps) applyPieceSkin(ps,false);
  refreshThemeSelections();
}

function applySiteTheme(id,save=true){
  const body=document.body;
  SITE_THEMES.forEach(t=>body.classList.remove(t.id));
  if(id!=='theme-darkgold') body.classList.add(id);
  currentSiteTheme=id;
  if(save) localStorage.setItem('dc-site-theme',id);
}
function applyBoardSkin(id,save=true){
  const board=document.getElementById('board');
  BOARD_SKINS.forEach(s=>board.classList.remove(s.id));
  board.classList.add(id);
  currentBoardSkin=id;
  if(save) localStorage.setItem('dc-board-skin',id);
}
function applyPieceSkin(id,save=true){
  const board=document.getElementById('board');
  PIECE_SKINS.forEach(s=>board.classList.remove(s.id));
  board.classList.add(id);
  currentPieceSkin=id;
  if(save) localStorage.setItem('dc-piece-skin',id);
}
function refreshThemeSelections(){
  document.querySelectorAll('#site-theme-grid .theme-swatch').forEach(el=>{
    el.classList.toggle('active',el.dataset.id===currentSiteTheme);
  });
  document.querySelectorAll('#board-skin-grid .theme-swatch').forEach(el=>{
    el.classList.toggle('active',el.dataset.id===currentBoardSkin);
  });
  document.querySelectorAll('#piece-skin-grid .theme-swatch').forEach(el=>{
    el.classList.toggle('active',el.dataset.id===currentPieceSkin);
  });
}

function buildThemeModal(){
  // Site themes
  const stg=document.getElementById('site-theme-grid');
  SITE_THEMES.forEach(t=>{
    const sw=document.createElement('div');
    sw.className='theme-swatch'; sw.dataset.id=t.id;
    sw.innerHTML=`<div class="swatch-preview"><div class="swatch-top" style="background:${t.bg}"></div><div class="swatch-bot" style="background:${t.accent}"></div></div><div class="swatch-label">${t.name}</div>`;
    sw.onclick=()=>{applySiteTheme(t.id);refreshThemeSelections();};
    stg.appendChild(sw);
  });
  // Board skins
  const bsg=document.getElementById('board-skin-grid');
  BOARD_SKINS.forEach(s=>{
    const sw=document.createElement('div');
    sw.className='theme-swatch'; sw.dataset.id=s.id;
    sw.innerHTML=`<div class="board-swatch-preview" style="border-color:var(--border)"><div style="background:${s.a}"></div><div style="background:${s.b}"></div><div style="background:${s.b}"></div><div style="background:${s.a}"></div></div><div class="swatch-label">${s.name}</div>`;
    sw.onclick=()=>{applyBoardSkin(s.id);refreshThemeSelections();};
    bsg.appendChild(sw);
  });
  // Piece skins
  const psg=document.getElementById('piece-skin-grid');
  PIECE_SKINS.forEach(s=>{
    const sw=document.createElement('div');
    sw.className='theme-swatch'; sw.dataset.id=s.id;
    const preview=document.createElement('div');
    preview.className='piece-swatch-preview'; preview.style.fontSize='1.5rem';
    preview.innerHTML=`<span class="${s.id} piece w" style="font-size:1.5rem;line-height:1">${s.preview}</span>`;
    sw.appendChild(preview);
    const label=document.createElement('div');
    label.className='swatch-label'; label.textContent=s.name;
    sw.appendChild(label);
    sw.onclick=()=>{applyPieceSkin(s.id);refreshThemeSelections();};
    psg.appendChild(sw);
  });
  refreshThemeSelections();
}

// ══════════════════════════════════════════════════════════════
//  UI RENDERING
// ══════════════════════════════════════════════════════════════
const boardEl=document.getElementById('board');
const rankToDisplay=row=>SIZE-row;
const fileToDisplay=col=>String.fromCharCode(97+col);

function renderBoard(){
  boardEl.innerHTML='';
  const {board,selected,legalMoves,flipped,lastMove,inCheck,turn,aiColor,aiThinking,mpMode,mpColor}=state;
  const kingPos=findKing(board,turn);
  const isMyTurn=mpMode?(turn===mpColor):(!aiColor||turn!==aiColor);

  for(let dr=0;dr<SIZE;dr++){
    for(let dc=0;dc<SIZE;dc++){
      const r=flipped?SIZE-1-dr:dr, c=flipped?SIZE-1-dc:dc;
      const sq=document.createElement('div');
      sq.classList.add('sq',(r+c)%2===0?'light':'dark');
      sq.dataset.r=r; sq.dataset.c=c;
      if(dc===0){const s=document.createElement('span');s.className='coord-rank';s.textContent=rankToDisplay(r);sq.appendChild(s);}
      if(dr===SIZE-1){const s=document.createElement('span');s.className='coord-file';s.textContent=fileToDisplay(c);sq.appendChild(s);}
      if(lastMove&&((lastMove.fromR===r&&lastMove.fromC===c)||(lastMove.toR===r&&lastMove.toC===c))) sq.classList.add('last-move');
      if(selected&&selected[0]===r&&selected[1]===c) sq.classList.add('selected');
      if(inCheck&&kingPos&&kingPos[0]===r&&kingPos[1]===c) sq.classList.add('in-check');
      const lm=legalMoves.find(m=>m.row===r&&m.col===c);
      if(lm&&isMyTurn&&!aiThinking){
        if(lm.special==='archer_ranged'||(board[r][c]&&board[r][c].color!==board[selected?.[0]][selected?.[1]]?.color&&lm.special!=='portal_swap'))
          sq.classList.add('legal-capture');
        else sq.classList.add('legal-move');
        sq.classList.add('hover-hint');
      } else if(!(selected&&selected[0]===r&&selected[1]===c)){
        if(board[r][c]?.color===turn&&isMyTurn&&!aiThinking) sq.classList.add('hover-hint');
      }
      const p=board[r][c];
      if(p){
        const pd=document.createElement('span');
        pd.className=`piece ${p.color}`;
        pd.textContent=GLYPHS[p.color][p.type];
        if(p.color===BLACK&&GLYPH_EMOJI.has(p.type)) pd.style.filter='brightness(0.4) sepia(1)';
        sq.appendChild(pd);
      }
      sq.addEventListener('click',onSquareClick);
      boardEl.appendChild(sq);
    }
  }
}

function renderStatus(){
  const bar=document.getElementById('status-bar');
  if(state.gameOver||state.aiThinking) return;
  const who=state.turn===WHITE?'White':'Black';
  const isAI=state.aiColor&&state.turn===state.aiColor;
  const isRemote=state.mpMode&&state.turn!==state.mpColor;
  if(state.inCheck){bar.textContent=`${who} is in CHECK!`;bar.classList.add('check');}
  else if(isAI){bar.textContent=`🤖 AI (${who})'s Turn`;bar.classList.remove('check');}
  else if(isRemote){bar.textContent=`⏳ Opponent's Turn (${who})`;bar.classList.remove('check');}
  else{bar.textContent=`${who}'s Turn`;bar.classList.remove('check');}
}
function renderMoveLog(){
  const log=document.getElementById('move-log');
  log.innerHTML='';
  state.moveLog.forEach((e,i)=>{
    const row=document.createElement('div');row.className='log-entry';
    row.innerHTML=`<span class="log-num">${i+1}.</span><span class="log-w">${e.white||''}</span><span class="log-b">${e.black||''}</span>`;
    log.appendChild(row);
  });
  log.scrollTop=log.scrollHeight;
}
function renderCaptured(){
  document.getElementById('captured-white').innerHTML=state.capturedByWhite.map(p=>`<span title="${PIECE_NAMES[p.type]}">${GLYPHS.b[p.type]}</span>`).join('');
  document.getElementById('captured-black').innerHTML=state.capturedByBlack.map(p=>`<span title="${PIECE_NAMES[p.type]}">${GLYPHS.w[p.type]}</span>`).join('');
}
function renderAll(){renderBoard();renderStatus();renderMoveLog();renderCaptured();}

// ── Legend ────────────────────────────────────────────────────
function buildLegend(){
  const el=document.getElementById('legend');
  [[KING,'King','1 sq any dir'],[QUEEN,'Queen','Any dir'],[ROOK,'Rook','H&V, any dist'],
   [KNIGHT,'Knight','L-shape'],[PAWN,'Pawn','Fwd 1–3 (once)'],[WIZARD,'Wizard','Bishop+Knight'],
   [DRAGON,'Dragon','Rook ≤4 sq'],[CHAMPION,'Champion','1–2 sq any'],[ARCHER,'Archer','Stationary shot 1–2'],[PORTAL,'Portal','Swap friend ≤3']
  ].forEach(([type,name,desc])=>{
    const div=document.createElement('div');div.className='legend-item';div.title=desc;
    div.innerHTML=`<span class="legend-glyph">${GLYPHS.w[type]}</span><span class="legend-name">${name}</span>`;
    el.appendChild(div);
  });
}

// ── Move notation ─────────────────────────────────────────────
function moveNotation(piece,fromR,fromC,toR,toC,special,cap){
  if(special==='castleK') return 'O-O';
  if(special==='castleQ') return 'O-O-O';
  if(special==='portal_swap') return `O${fileToDisplay(fromC)}${rankToDisplay(fromR)}⇌${fileToDisplay(toC)}${rankToDisplay(toR)}`;
  let s=PIECE_LETTERS[piece.type]+fileToDisplay(fromC)+rankToDisplay(fromR);
  s+=(cap?'x':'-')+fileToDisplay(toC)+rankToDisplay(toR);
  if(special==='promotion') s+='=?';
  if(special==='ep') s+=' e.p.';
  if(special==='archer_ranged') s+='⟶';
  return s;
}

// ── Click handler ─────────────────────────────────────────────
function onSquareClick(e){
  if(state.gameOver||state.pendingPromotion||state.aiThinking) return;
  if(state.aiColor&&state.turn===state.aiColor) return;
  if(state.mpMode&&state.turn!==state.mpColor) return;
  const sq=e.currentTarget;
  const r=parseInt(sq.dataset.r),c=parseInt(sq.dataset.c);
  const {board,turn,selected,legalMoves}=state;
  const piece=board[r][c];
  if(selected){
    const move=legalMoves.find(m=>m.row===r&&m.col===c);
    if(move){executeMove(selected[0],selected[1],r,c,move.special,false);return;}
    if(piece&&piece.color===turn){selectPiece(r,c);return;}
    state.selected=null;state.legalMoves=[];renderAll();return;
  }
  if(piece&&piece.color===turn) selectPiece(r,c);
}
function selectPiece(r,c){
  state.selected=[r,c];
  state.legalMoves=getLegalMoves(state.board,r,c,state.enPassantTarget);
  renderAll();
}

// ── Execute move ──────────────────────────────────────────────
function executeMove(fromR,fromC,toR,toC,special,isAI,forcedPromo){
  const {board}=state;
  const piece=board[fromR][fromC];
  const capturedPiece=special==='archer_ranged'?board[toR][toC]:special==='ep'?board[toR+(piece.color===WHITE?1:-1)][toC]:special==='portal_swap'?null:board[toR][toC];
  const notation=moveNotation(piece,fromR,fromC,toR,toC,special,capturedPiece&&capturedPiece.color!==piece.color?capturedPiece:null);
  let newEP=null;
  if(special==='double_push') newEP=[fromR+(piece.color===WHITE?-1:1),fromC];
  const newBoard=applyMove(board,fromR,fromC,toR,toC,special,state.enPassantTarget);
  if(capturedPiece&&capturedPiece.color!==piece.color){
    if(piece.color===WHITE) state.capturedByWhite.push(capturedPiece);
    else state.capturedByBlack.push(capturedPiece);
  }
  state.board=newBoard;state.enPassantTarget=newEP;
  state.lastMove={fromR,fromC,toR,toC};
  state.selected=null;state.legalMoves=[];
  // promotion check
  const moved=state.board[toR][toC];
  const promoRow=moved?.color===WHITE?0:9;
  if(moved?.type===PAWN&&toR===promoRow&&special!=='portal_swap'){
    state.pendingPromotion={row:toR,col:toC,color:moved.color,notation,fromR,fromC};
    renderAll();
    if(isAI||forcedPromo){
      const promoType=forcedPromo||QUEEN;
      doPromotion(promoType,notation,moved.color,toR,toC,fromR,fromC);
    } else {
      showPromotionModal(moved.color,fromR,fromC,toR,toC,notation);
    }
    return;
  }
  logMove(notation,piece.color);
  switchTurn(fromR,fromC,toR,toC,special,null);
}

function doPromotion(type,notation,color,row,col,fromR,fromC){
  state.board[row][col]=makePiece(type,color);
  state.board[row][col].hasMoved=true;
  const fullNote=notation.replace('=?',`=${PIECE_LETTERS[type]}`);
  logMove(fullNote,color);
  state.pendingPromotion=null;
  document.getElementById('promotion-modal').classList.add('hidden');
  switchTurn(fromR,fromC,row,col,'promotion',type);
}

function logMove(notation,color){
  if(color===WHITE) state.moveLog.push({white:notation,black:''});
  else{if(state.moveLog.length>0)state.moveLog[state.moveLog.length-1].black=notation;else state.moveLog.push({white:'…',black:notation});}
}
function switchTurn(fromR,fromC,toR,toC,special,promoType){
  state.turn=state.turn===WHITE?BLACK:WHITE;
  const enemy=state.turn===WHITE?BLACK:WHITE;
  state.inCheck=isInCheck(state.board,state.turn,state.enPassantTarget);
  if(!hasAnyLegal(state.board,state.turn,state.enPassantTarget)){
    endGame(state.inCheck?'checkmate':'stalemate',enemy);return;
  }
  renderAll();
  maybeRunAI();
}

// ── Promotion modal ───────────────────────────────────────────
function showPromotionModal(color,fromR,fromC,toR,toC,notation){
  const modal=document.getElementById('promotion-modal');
  const choices=document.getElementById('promotion-choices');
  choices.innerHTML='';
  [QUEEN,WIZARD,DRAGON,CHAMPION,ARCHER].forEach(type=>{
    const btn=document.createElement('button');
    btn.className='promo-btn';
    btn.innerHTML=`<span class="promo-glyph">${GLYPHS[color][type]}</span><span>${PIECE_NAMES[type]}</span>`;
    btn.addEventListener('click',()=>{
      // if MP, send the promotion choice to opponent too
      if(state.mpMode) sendMove(fromR,fromC,toR,toC,'promotion',type);
      doPromotion(type,notation,color,toR,toC,fromR,fromC);
    });
    choices.appendChild(btn);
  });
  modal.classList.remove('hidden');
}

// Override executeMove to also send move over network for local player
const _origExec=executeMove;
// Patch: wrap click-triggered moves to send to peer
function onSquareClickMove(fromR,fromC,toR,toC,special){
  executeMove(fromR,fromC,toR,toC,special,false);
  // send after execution (non-promo moves)
  const moved=state.board[toR]?.[toC];
  const promoRow=moved?.color===WHITE?0:9;
  const isPromo=moved?.type===PAWN&&toR===promoRow;
  if(!isPromo) sendMove(fromR,fromC,toR,toC,special,null);
}

// Re-wire click handler to use patched version
function onSquareClick(e){
  if(state.gameOver||state.pendingPromotion||state.aiThinking) return;
  if(state.aiColor&&state.turn===state.aiColor) return;
  if(state.mpMode&&state.turn!==state.mpColor) return;
  const sq=e.currentTarget;
  const r=parseInt(sq.dataset.r),c=parseInt(sq.dataset.c);
  const {board,turn,selected,legalMoves}=state;
  const piece=board[r][c];
  if(selected){
    const move=legalMoves.find(m=>m.row===r&&m.col===c);
    if(move){onSquareClickMove(selected[0],selected[1],r,c,move.special);return;}
    if(piece&&piece.color===turn){selectPiece(r,c);return;}
    state.selected=null;state.legalMoves=[];renderAll();return;
  }
  if(piece&&piece.color===turn) selectPiece(r,c);
}

// ── Game over ─────────────────────────────────────────────────
function endGame(reason,winner){
  state.gameOver=true;
  const title=document.getElementById('game-over-title');
  const msg=document.getElementById('game-over-msg');
  if(reason==='checkmate'){title.textContent='Checkmate!';msg.textContent=(winner===WHITE?'White':'Black')+' wins!';}
  else if(reason==='stalemate'){title.textContent='Stalemate!';msg.textContent='The game is a draw.';}
  else if(reason==='resign'){title.textContent='Resignation!';msg.textContent='Your opponent resigned. You win!';}
  document.getElementById('status-bar').textContent=title.textContent;
  document.getElementById('status-bar').classList.remove('check');
  document.getElementById('game-over-modal').classList.remove('hidden');
  renderBoard();
}

// ── New game / buttons ────────────────────────────────────────
function getSetupSettings(){
  const mode=document.querySelector('.mode-btn.active')?.dataset.mode||'2p';
  const level=parseInt(document.querySelector('.level-btn.active')?.dataset.level||'3');
  return{mode,level};
}
function updateAIBadge(){
  const badge=document.getElementById('ai-badge');
  const names=['','Easy','Medium','Hard','Super Hard','Impossible'];
  if(state.aiColor){badge.textContent=`🤖 AI: ${names[state.aiLevel]}`;badge.style.display='inline-block';}
  else badge.style.display='none';
}
function startNewGame(){
  document.getElementById('game-over-modal').classList.add('hidden');
  document.getElementById('promotion-modal').classList.add('hidden');
  const{mode,level}=getSetupSettings();
  // Don't reset MP game mid-connection
  if(mode==='mp'&&!state.mpConnected){
    document.getElementById('mp-modal').classList.remove('hidden');
    return;
  }
  initState();
  if(mode==='ai'){state.aiColor=BLACK;state.aiLevel=level;}
  if(mode==='mp'&&state.mpConnected){
    state.mpMode=true;state.mpColor=mpIsHost?WHITE:BLACK;
    state.flipped=!mpIsHost;
  }
  document.getElementById('mp-badge').style.display='none';
  document.getElementById('mp-info-bar').style.display='none';
  applyBoardSkin(currentBoardSkin,false);
  applyPieceSkin(currentPieceSkin,false);
  updateAIBadge();
  renderAll();
}

document.getElementById('btn-new-game').addEventListener('click',startNewGame);
document.getElementById('btn-flip').addEventListener('click',()=>{state.flipped=!state.flipped;renderBoard();});
document.getElementById('btn-rules').addEventListener('click',()=>document.getElementById('rules-modal').classList.remove('hidden'));
document.getElementById('close-rules').addEventListener('click',()=>document.getElementById('rules-modal').classList.add('hidden'));
document.getElementById('btn-play-again').addEventListener('click',startNewGame);
document.getElementById('btn-theme').addEventListener('click',()=>{document.getElementById('theme-modal').classList.remove('hidden');refreshThemeSelections();});
document.getElementById('rules-modal').addEventListener('click',e=>{if(e.target===document.getElementById('rules-modal'))document.getElementById('rules-modal').classList.add('hidden');});
document.getElementById('theme-modal').addEventListener('click',e=>{if(e.target===document.getElementById('theme-modal'))document.getElementById('theme-modal').classList.add('hidden');});

// Level buttons
document.querySelectorAll('.level-btn').forEach(btn=>{
  btn.addEventListener('click',()=>{document.querySelectorAll('.level-btn').forEach(b=>b.classList.remove('active'));btn.classList.add('active');});
});

// ── Init ──────────────────────────────────────────────────────
buildLegend();
buildThemeModal();
initState();
applyBoardSkin('board-classic',false);
applyPieceSkin('skin-classic',false);
loadSavedPrefs();
renderAll();
