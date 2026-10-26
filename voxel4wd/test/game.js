/* ボクセル四駆 3D core: ボクセル車体 / 空力(真横・真上) / 立体レーンチェンジ コース / 走行シミュレーション */
(function (root) {
'use strict';

/* ---------- ブロックグリッド ----------
   つくる単位は 1ブロック = 10mm の立方体 (16 x 6 x 10 ブロック)。
   空力・重さの計算は、それを 5mm の細かいマスに割った (32 x 12 x 20) 上で行う。 */
const CELL_MM = 5, BS = 2;
const CX = 32, CY = 12, CZ = 20;                  // 細かいマス: 前後160mm 高さ60mm 幅100mm
const NX = CX / BS, NY = CY / BS, NZ = CZ / BS;   // ブロックの数
const ZC = CZ / 2, BZC = NZ / 2;                  // 幅の中心 (細かいマス / ブロック)
const M_BODY = 1, M_WING = 1, M_WEIGHT = 3;       // 素材は プラスチック(1) と 鉄(3) の2種類
const L_AXLE = 6, L_FLOOR = 7, L_CHASSIS = 8, L_WHEEL = 9;
const MASS_G = [0, 0.04, 0.04, 0.16];             // 細かいマス1つあたり (1ブロック = 8マス)
const BASE_MASS = 50;
const LIM = { minW: 70, maxW: 140 };
const WHEELS = [{ cx: 7, cy: 3, r: 3 }, { cx: 25, cy: 3, r: 3 }];
const WHEEL_Z = [1, 19], WHEEL_W = 2;             // タイヤの幅方向の中心と幅 (細かいマス)
const BASE_CGX = 16, BASE_CGY = 2.0;
const N = NX * NY * NZ, CN = CX * CY * CZ;
const I = (x, y, z) => x + NX * (y + NY * z);       // ブロックの番号
const CI = (x, y, z) => x + CX * (y + CY * z);      // 細かいマスの番号

/* ブロックごとのロック: フレーム・タイヤ・地面すれすれの段 */
const LOCK = new Uint8Array(N);
{
  const FY = 1;
  for (const x of [3, 12]) for (let z = 1; z <= NZ - 2; z++) LOCK[I(x, FY, z)] = L_CHASSIS;
  for (const z of [NZ / 2 - 1, NZ / 2]) for (let x = 3; x <= 12; x++) LOCK[I(x, FY, z)] = L_CHASSIS;
  for (const w of WHEELS) {
    const x0 = Math.floor((w.cx - w.r) / BS), x1 = Math.floor((w.cx + w.r - 0.01) / BS), y1 = Math.floor((w.cy + w.r - 0.01) / BS);
    for (let y = 0; y <= y1; y++) for (let x = x0; x <= x1; x++) for (const z of [0, NZ - 1]) LOCK[I(x, y, z)] = L_WHEEL;
  }
  for (let z = 0; z < NZ; z++) for (let x = 0; x < NX; x++) if (!LOCK[I(x, 0, z)]) LOCK[I(x, 0, z)] = L_FLOOR;
}
/* 細かいマス側のロック (空力・連結の計算用) */
const LOCKC = new Uint8Array(CN);
for (let z = 0; z < NZ; z++) for (let y = 0; y < NY; y++) for (let x = 0; x < NX; x++) {
  const lk = LOCK[I(x, y, z)]; if (lk !== L_CHASSIS && lk !== L_FLOOR) continue;
  for (let dz = 0; dz < BS; dz++) for (let dy = 0; dy < BS; dy++) for (let dx = 0; dx < BS; dx++) LOCKC[CI(x * BS + dx, y * BS + dy, z * BS + dz)] = lk;
}
for (const w of WHEELS) {
  for (let y = 0; y < CY; y++) for (let x = 0; x < CX; x++) {
    const dx = x + 0.5 - w.cx, dy = y + 0.5 - w.cy;
    if (dx * dx + dy * dy <= w.r * w.r + 0.01) for (const z of [0, 1, CZ - 2, CZ - 1]) LOCKC[CI(x, y, z)] = L_WHEEL;
  }
}

const inGrid = (x, y, z) => x >= 0 && y >= 0 && z >= 0 && x < NX && y < NY && z < NZ;
const cInGrid = (x, y, z) => x >= 0 && y >= 0 && z >= 0 && x < CX && y < CY && z < CZ;
const isLocked = (x, y, z) => LOCK[I(x, y, z)] !== 0;
const isFrame = k => k === L_CHASSIS || k === L_AXLE || k === L_WHEEL;
const clamp = (v, a, b) => Math.max(a, Math.min(b, v));

const SHAPE_TYPES = [{ id: 'cube', name: '立方体' }, { id: 'half', name: 'ハーフ' }, { id: 'tri', name: '三角' }, { id: 'pyr', name: '四角錐' }, { id: 'cyl', name: '円柱' }];
const SHAPES = [];
const SHAPE_START = {}, SHAPE_COUNT = {};
(function buildShapes() {
  const rots = [];
  [[0, 1, 2], [0, 2, 1], [1, 0, 2], [1, 2, 0], [2, 0, 1], [2, 1, 0]].forEach(perm => {
    const parity = ((perm[0] > perm[1]) + (perm[0] > perm[2]) + (perm[1] > perm[2])) % 2 ? -1 : 1;
    for (let sx = -1; sx <= 1; sx += 2) for (let sy = -1; sy <= 1; sy += 2) for (let sz = -1; sz <= 1; sz += 2)
      if (parity * sx * sy * sz === 1) rots.push({ perm, sg: [sx, sy, sz] });
  });
  rots.sort((a, b) => (b.perm.join() === '0,1,2' && b.sg.join() === '1,1,1') - (a.perm.join() === '0,1,2' && a.sg.join() === '1,1,1'));
  const ap = (R, v) => [0, 1, 2].map(i => R.sg[i] * (v[R.perm[i]] - 0.5) + 0.5);
  const quad = (a, b, c, d) => [a, b, c, d];
  const boxF = (x0, y0, z0, x1, y1, z1) => [
    quad([x0, y0, z0], [x1, y0, z0], [x1, y0, z1], [x0, y0, z1]), quad([x0, y1, z0], [x0, y1, z1], [x1, y1, z1], [x1, y1, z0]),
    quad([x0, y0, z0], [x0, y1, z0], [x1, y1, z0], [x1, y0, z0]), quad([x0, y0, z1], [x1, y0, z1], [x1, y1, z1], [x0, y1, z1]),
    quad([x0, y0, z0], [x0, y0, z1], [x0, y1, z1], [x0, y1, z0]), quad([x1, y0, z0], [x1, y1, z0], [x1, y1, z1], [x1, y0, z1])];
  const CYL_N = 16, cylR = 0.5, cylP = (i, y) => [0.5 + cylR * Math.cos(2 * Math.PI * i / CYL_N), y, 0.5 + cylR * Math.sin(2 * Math.PI * i / CYL_N)];
  const cylFaces = () => {
    const top = [], bot = [], out = [];
    for (let i = 0; i < CYL_N; i++) { top.push(cylP(i, 1)); bot.push(cylP(CYL_N - 1 - i, 0)); }
    out.push(top, bot);
    for (let i = 0; i < CYL_N; i++) out.push([cylP(i, 0), cylP(i, 1), cylP(i + 1, 1), cylP(i + 1, 0)]);
    return out;
  };
  const canon = {
    cube: { faces: boxF(0, 0, 0, 1, 1, 1), inside: () => true },
    half: { faces: boxF(0, 0, 0, 1, 0.5, 1), inside: c => c[1] < 0.5 },
    tri: { faces: [[[0, 0, 1], [1, 0, 1], [0, 1, 1]], [[0, 0, 0], [0, 1, 0], [1, 0, 0]], quad([0, 0, 0], [1, 0, 0], [1, 0, 1], [0, 0, 1]),
      quad([0, 0, 0], [0, 0, 1], [0, 1, 1], [0, 1, 0]), quad([1, 0, 0], [0, 1, 0], [0, 1, 1], [1, 0, 1])], inside: c => c[0] + c[1] <= 1.0001 },
    cyl: { faces: cylFaces(), inside: () => true },
    pyr: { faces: [quad([0, 0, 0], [1, 0, 0], [1, 0, 1], [0, 0, 1]), [[0, 0, 0], [0.5, 1, 0.5], [1, 0, 0]], [[1, 0, 0], [0.5, 1, 0.5], [1, 0, 1]],
      [[1, 0, 1], [0.5, 1, 0.5], [0, 0, 1]], [[0, 0, 1], [0.5, 1, 0.5], [0, 0, 0]]], inside: c => c[1] < 0.5 }
  };
  const sig = faces => { const set = new Set(); faces.forEach(f => f.forEach(v => set.add(v.map(q => (Math.round(q * 1000) / 1000 + 0).toFixed(3)).join(',')))); return [...set].sort().join('|'); };
  const finish = (faces) => {
    const pts = []; faces.forEach(f => f.forEach(v => pts.push(v)));
    const cen = [0, 1, 2].map(i => pts.reduce((a, v) => a + v[i], 0) / pts.length);
    return faces.map(f => {
      let v = f.map(q => q.slice());
      const u = [v[1][0] - v[0][0], v[1][1] - v[0][1], v[1][2] - v[0][2]], w = [v[2][0] - v[0][0], v[2][1] - v[0][1], v[2][2] - v[0][2]];
      let n = [u[1] * w[2] - u[2] * w[1], u[2] * w[0] - u[0] * w[2], u[0] * w[1] - u[1] * w[0]];
      const fc = [0, 1, 2].map(i => v.reduce((a, q) => a + q[i], 0) / v.length);
      if (n[0] * (fc[0] - cen[0]) + n[1] * (fc[1] - cen[1]) + n[2] * (fc[2] - cen[2]) < 0) { v = v.reverse(); n = n.map(q => -q); }
      const l = Math.hypot(...n) || 1; return { v, n: n.map(q => q / l) };
    });
  };
  const SIG = {};
  for (const t of SHAPE_TYPES) {
    const seen = new Map(); SHAPE_START[t.id] = SHAPES.length; SHAPE_COUNT[t.id] = 0;
    for (const R of (t.id === 'cube' ? [rots[0]] : rots)) {
      const faces = canon[t.id].faces.map(f => f.map(v => ap(R, v)));
      const sg = sig(faces); if (seen.has(sg)) continue; seen.set(sg, 1);
      let mask = 0;
      for (let k = 0; k < 8; k++) {
        const c = [(k & 1) ? 0.75 : 0.25, (k & 2) ? 0.75 : 0.25, (k & 4) ? 0.75 : 0.25];
        if (!canon[t.id].inside(c)) continue;
        const d = ap(R, c); mask |= 1 << ((d[0] > 0.5 ? 1 : 0) + (d[1] > 0.5 ? 2 : 0) + (d[2] > 0.5 ? 4 : 0));
      }
      SHAPES.push({ type: t.id, ori: SHAPE_COUNT[t.id]++, mask: t.id === 'cube' ? 255 : mask, faces: finish(faces).map(f => (f.soft = t.id === 'cyl' && f.v.length === 4, f)), sig: sg });
      SIG[t.id + '#' + sg] = SHAPES.length - 1;
    }
  }
  SHAPES.forEach(sh => {
    const mf = sh.faces.map(f => f.v.map(v => [v[0], v[1], 1 - v[2]]));
    sh.mirror = SIG[sh.type + '#' + sig(mf)];
  });
})();
const shapeCode = (type, ori) => SHAPE_START[type] + ((ori % SHAPE_COUNT[type]) + SHAPE_COUNT[type]) % SHAPE_COUNT[type];
const newShapes = () => new Uint8Array(N);

function expand(bg, sg) {
  const c = new Uint8Array(CN);
  for (let z = 0; z < NZ; z++) for (let y = 0; y < NY; y++) for (let x = 0; x < NX; x++) {
    const i = I(x, y, z), m = bg[i]; if (!m) continue;
    const mask = sg && sg[i] ? SHAPES[sg[i]].mask : 255;
    for (let dz = 0; dz < BS; dz++) for (let dy = 0; dy < BS; dy++) for (let dx = 0; dx < BS; dx++)
      if (mask & (1 << (dx + 2 * dy + 4 * dz))) c[CI(x * BS + dx, y * BS + dy, z * BS + dz)] = m;
  }
  return c;
}

function floatBlocks(user) {
  const seen = new Uint8Array(CN), q = [];
  for (let k = 0; k < CN; k++) if (isFrame(LOCKC[k])) { seen[k] = 1; q.push(k); }
  while (q.length) {
    const k = q.pop(), x = k % CX, y = ((k / CX) | 0) % CY, z = (k / (CX * CY)) | 0;
    for (let dz = -1; dz <= 1; dz++) for (let dy = -1; dy <= 1; dy++) for (let dx = -1; dx <= 1; dx++) {
      const xx = x + dx, yy = y + dy, zz = z + dz;
      if (!cInGrid(xx, yy, zz)) continue;
      const kk = CI(xx, yy, zz);
      if (seen[kk] || user[kk] === 0) continue;
      seen[kk] = 1; q.push(kk);
    }
  }
  const fset = new Set();
  for (let k = 0; k < CN; k++) if (user[k] > 0 && !seen[k]) {
    const x = k % CX, y = ((k / CX) | 0) % CY, z = (k / (CX * CY)) | 0;
    fset.add(I(Math.floor(x / BS), Math.floor(y / BS), Math.floor(z / BS)));
  }
  return [...fset];
}
const floaters = (bg, sg) => floatBlocks(expand(bg, sg));

const isHalf = code => !!code && SHAPES[code].type === 'half';
function halfOpen(code) {
  const sh = SHAPES[code]; let m = [0, 0, 0];
  for (let k = 0; k < 8; k++) if (sh.mask & (1 << k)) { m[0] += (k & 1) - 0.5; m[1] += ((k >> 1) & 1) - 0.5; m[2] += ((k >> 2) & 1) - 0.5; }
  return m.map(q => -Math.sign(Math.round(q * 100) / 100));
}

const NOSE_BLUNT_REF = 7;
const flatFront = code => { if (!code) return true; const sh = SHAPES[code]; if (sh.type === 'cyl') return true; return sh.faces.some(f => f.n[0] > 0.95); };
const BL = 0.007;
function analyze(ub, us) {
  const user = expand(ub, us);
  const counts = [0, 0, 0, 0];
  let mDraw = 0, mx = 0, my = 0, mz = 0;
  const PN = CX + 2;
  const top = new Array(PN).fill(0), bot = new Array(PN).fill(99);
  const zr = new Array(PN).fill(0), zl = new Array(PN).fill(0);
  const zmaxA = new Array(PN).fill(-1), zminA = new Array(PN).fill(99);
  const plan = new Uint8Array(CX * CZ);
  const secA = new Uint16Array(CX), sideCols = new Uint8Array(CX * CY);
  let minX = 99, maxX = -1, minY = 99, maxY = -1, minZ = 99, maxZ = -1;
  for (let z = 0; z < CZ; z++) for (let y = 0; y < CY; y++) for (let x = 0; x < CX; x++) {
    const k = CI(x, y, z), u = user[k], lk = LOCKC[k];
    if (u >= 1 && u <= 3) {
      counts[u]++;
      const m = MASS_G[u]; mDraw += m; mx += m * (x + 0.5); my += m * (y + 0.5); mz += m * (z + 0.5);
      if (y >= 2) plan[x + CX * z] = 1;
    }
    if (u > 0 || (isFrame(lk) && lk !== L_WHEEL)) { secA[x]++; sideCols[x + CX * y] = 1; }
    if (u > 0 || isFrame(lk)) {
      if (y + 1 > top[x + 1]) top[x + 1] = y + 1;
      if (y < bot[x + 1] && lk !== L_WHEEL) bot[x + 1] = y;
      if (z > zmaxA[x + 1]) zmaxA[x + 1] = z;
      if (z < zminA[x + 1]) zminA[x + 1] = z;
      if (x < minX) minX = x; if (x > maxX) maxX = x; if (y < minY) minY = y; if (y > maxY) maxY = y;
      if (z < minZ) minZ = z; if (z > maxZ) maxZ = z;
    }
  }
  const mass = BASE_MASS + mDraw;
  let blocks = 0; for (let i = 0; i < ub.length; i++) if (ub[i] > 0) blocks++;
  let sideArea = 0; for (let i = 0; i < sideCols.length; i++) sideArea += sideCols[i];
  let bluntW = 0;
  { const hits = []; let xf = -1;
    for (let z = 0; z < NZ; z++) for (let y = 0; y < NY; y++) {
      for (let x = NX - 1; x >= 0; x--) {
        const k = I(x, y, z), lk = LOCK[k];
        if (ub[k] > 0) { hits.push([x, flatFront(us ? us[k] : 0)]); if (x > xf) xf = x; break; }
        if (isFrame(lk) && lk !== L_WHEEL) { hits.push([x, true]); if (x > xf) xf = x; break; }
      }
    }
    const W = [1, 0.6, 0.3, 0.1];
    for (const [x, flat] of hits) { const d = xf - x; if (flat && d < W.length) bluntW += W[d]; }
  }
  const nose = clamp(1 - bluntW / NOSE_BLUNT_REF, 0, 1);
  const cgx = (BASE_MASS * BASE_CGX + mx) / mass, cgy = (BASE_MASS * BASE_CGY + my) / mass, cgz = (BASE_MASS * ZC + mz) / mass;
  for (let i = 0; i < PN; i++) {
    if (zmaxA[i] >= 0) { zr[i] = zmaxA[i] + 1 - ZC; zl[i] = ZC - zminA[i]; }
  }
  let planArea = 0, pcx = 0;
  for (let x = 0; x < CX; x++) for (let z = 0; z < CZ; z++) if (plan[x + CX * z]) { planArea++; pcx += x + 0.5; }
  pcx = planArea ? pcx / planArea : cgx;

  const aMax = new Array(PN), aMin = new Array(PN), rMax = new Array(PN), lMax = new Array(PN);
  for (let j = PN - 1; j >= 0; j--) {
    aMax[j] = Math.max(top[j], j + 1 < PN ? aMax[j + 1] : 0);
    aMin[j] = Math.min(bot[j], j + 1 < PN ? aMin[j + 1] : 99);
    rMax[j] = Math.max(zr[j], j + 1 < PN ? rMax[j + 1] : 0);
    lMax[j] = Math.max(zl[j], j + 1 < PN ? lMax[j + 1] : 0);
  }
  const side = [];
  let sFx = 0, sFy = 0, sM = 0;
  const addS = (x, y, fx, fy, kind) => {
    if (!fx && !fy) return; sFx += fx; sFy += fy; sM += (x - cgx) * fy - (y - cgy) * fx; side.push({ x, y, fx, fy, kind });
  };
  for (let i = 0; i < PN - 1; i++) {
    const a = top[i], b = top[i + 1], dh = b - a;
    if (dh < 0) {
      const sh = (i + 2 < PN ? aMax[i + 2] : 0) > Math.max(a, b) ? 0.2 : 1;
      addS(i, (a + b) / 2, -(0.5 + Math.max(0, -dh - 1)) * sh, -0.5 * sh, 'top');
    } else if (dh > 0) addS(i, (a + b) / 2, -0.12 * dh, 0, 'wake');
    if (bot[i] < 99 && bot[i + 1] < 99) {
      const db = bot[i + 1] - bot[i];
      if (db > 0) {
        const sh = (i + 2 < PN ? aMin[i + 2] : 99) < Math.min(bot[i], bot[i + 1]) ? 0.2 : 1;
        addS(i, (bot[i] + bot[i + 1]) / 2, -(0.5 + Math.max(0, db - 1)) * sh, 0.5 * sh, 'under');
      }
    }
  }
  const planP = [];
  let pFx = 0, pFz = 0, pM = 0, pxw = 0, pw = 0;
  const addP = (x, z, fx, fz) => {
    if (!fx && !fz) return; pFx += fx; pFz += fz; pM += (x - cgx) * fz - (z - cgz) * fx;
    pxw += x * Math.abs(fx); pw += Math.abs(fx); planP.push({ x, z, fx, fz });
  };
  const edge = (arr, mx_, sign) => {
    for (let i = 0; i < PN - 1; i++) {
      const a = arr[i], b = arr[i + 1], dd = b - a;
      if (dd < 0) {
        const sh = (i + 2 < PN ? mx_[i + 2] : 0) > Math.max(a, b) ? 0.2 : 1;
        addP(i, ZC + sign * (a + b) / 2, -(0.5 + Math.max(0, -dd - 1)) * sh, -sign * 0.5 * sh);
      } else if (dd > 0) addP(i, ZC + sign * (a + b) / 2, -0.12 * dd, 0);
    }
  };
  edge(zr, rMax, 1); edge(zl, lMax, -1);
  const Dside = -sFx, Dplan = -pFx;
  const D = 1.0 + Dside * 0.7 + Dplan * 0.18;
  const baseLift = BL * planArea;
  const UB = 1.0, UBM = 10;
  const Fy = sFy + baseLift + UB;
  const M = sM + baseLift * (pcx - cgx) + UBM;
  const xcp = pw ? pxw / pw : cgx;
  const yawStab = clamp((xcp - cgx) / 8, -1, 1);

  const floatCells = floatBlocks(user);

  const dims = { len: (maxX - minX + 1) * CELL_MM, wid: (maxZ - minZ + 1) * CELL_MM, hgt: (maxY + 1) * CELL_MM };
  const rules = { weightMin: mass >= LIM.minW - 1e-9, weightMax: mass <= LIM.maxW + 1e-9, connected: floatCells.length === 0 };
  rules.ok = rules.weightMin && rules.weightMax && rules.connected;
  return {
    mass, cgx, cgy, cgz, cgBias: (cgx - BASE_CGX) / 10, cgzOff: (cgz - ZC) * 0.005, hcg: (cgy + 1.2) * 0.005,
    D, Dside, Dplan, Fy, M, baseLift, yawStab, xcp, Fz: pFz, Mz: pM, counts, planArea, dims, floatCells, rules, blocks, sideArea, nose, mUser: mDraw,
    side, planP, top: top.slice(1, CX + 1), bot: bot.slice(1, CX + 1)
  };
}

const COURSE = (function () {
  const STR = 4.4, RAD = 1.45;
  const segs = [];
  let x = 0, y = 0, h = 0, s = 0;
  function line(len) { segs.push({ k: 'L', s0: s, len, x0: x, y0: y, h0: h }); x += Math.cos(h) * len; y += Math.sin(h) * len; s += len; }
  function arc(r) {
    const len = Math.PI / 2 * r;
    segs.push({ k: 'A', s0: s, len, x0: x, y0: y, h0: h, R: r });
    const cx = x - r * Math.sin(h), cy = y + r * Math.cos(h);
    h += Math.PI / 2; x = cx + r * Math.sin(h); y = cy - r * Math.cos(h); s += len;
  }
  line(STR); arc(RAD); arc(RAD); line(STR); arc(RAD); arc(RAD);
  const length = s;
  const D2R = Math.PI / 180;
  const F = {
    lanes: [{ s0: 0.35, len: 3.5, A: 0.20 }, { s0: 11.0, len: 2.3, A: 0.11 }],
    jump: { s0: 0.8, rampLen: 0.6, ang: 16, gap: 0.0, landLen: 1.1, downAng: 8 },
    wave: { s0: 9.3, s1: 10.8, amp: 0.009, lam: 0.27, limit: 0.040 },
    width: 0.40
  };
  const segAt = sl => { for (let i = 0; i < segs.length; i++) if (sl < segs[i].s0 + segs[i].len) return segs[i]; return segs[segs.length - 1]; };
  function laneOff(sl) {
    let o = 0;
    for (const f of F.lanes) if (sl >= f.s0 && sl <= f.s0 + f.len) o += f.A * Math.sin(2 * Math.PI * (sl - f.s0) / f.len);
    return o;
  }
  function laneSlope(sl) {
    let o = 0;
    for (const f of F.lanes) if (sl >= f.s0 && sl <= f.s0 + f.len) { const w = 2 * Math.PI / f.len; o += f.A * w * Math.cos(w * (sl - f.s0)); }
    return o;
  }
  function inLane(sl) { return F.lanes.some(f => sl >= f.s0 && sl <= f.s0 + f.len); }
  function kappa(sl) {
    const sg = segAt(sl);
    if (sg.k === 'A') return 1 / sg.R;
    let k = 0;
    for (const f of F.lanes) if (sl >= f.s0 && sl <= f.s0 + f.len) { const w = 2 * Math.PI / f.len; k += -f.A * w * w * Math.sin(w * (sl - f.s0)); }
    return k;
  }
  function phi(sl) {
    const j = F.jump;
    if (sl >= j.s0 && sl < j.s0 + j.rampLen) return j.ang * D2R;
    if (sl >= j.s0 + j.rampLen + j.gap && sl < j.s0 + j.rampLen + j.gap + j.landLen) return -j.downAng * D2R;
    return 0;
  }
  const waveAt = sl => (sl >= F.wave.s0 && sl <= F.wave.s1) ? F.wave : null;
  function pos(s, lat) {
    const sl = ((s % length) + length) % length;
    const sg = segAt(sl), u = sl - sg.s0;
    let px, py, hd;
    if (sg.k === 'L') { px = sg.x0 + Math.cos(sg.h0) * u; py = sg.y0 + Math.sin(sg.h0) * u; hd = sg.h0; }
    else {
      const cx = sg.x0 - sg.R * Math.sin(sg.h0), cy = sg.y0 + sg.R * Math.cos(sg.h0);
      hd = sg.h0 + u / sg.R; px = cx + sg.R * Math.sin(hd); py = cy - sg.R * Math.cos(hd);
    }
    const off = laneOff(sl) + (lat || 0);
    const h2 = hd + (sg.k === 'L' ? Math.atan(laneSlope(sl)) : 0);
    return { x: px - Math.sin(hd) * off, y: py + Math.cos(hd) * off, h: h2, hd };
  }
  const ES = 0.02, EN = Math.ceil(length / ES) + 2, ET = new Float32Array(EN);
  for (let i = 1; i < EN; i++) ET[i] = ET[i - 1] + Math.sin(phi((i - 1) * ES)) * ES;
  const elev = s => { const sl = ((s % length) + length) % length, f = sl / ES, i = Math.floor(f); return ET[i] + (ET[i + 1] - ET[i]) * (f - i); };
  return { segs, length, F, kappa, phi, waveAt, pos, laneOff, inLane, elev, STR, RAD };
})();

const PHYS = {
  G: 9.8, F0: 1.5, V0: 5.6, MU_T: 0.9, MU_L: 0.7, CRR: 0.08, KD: 0.0046, KL: 0.018,
  HALF_TRACK: 0.030, K_GYR: 0.12, WALL_MU: 0.35,
  FAN_A: 16.5, FAN_BLOW: 0.9, FAN_WEIGHT: 2.3, FAN_TIP: 0, MAG_A: 20.0, BAR_LOSS: 0.97, BAR_EXP: 1.4, BAR_FLIP: 0.18, BAR_STUN: 1.5, BAR_BRAKE: 12.0,
  ITEM_KO_PROB: 0.25
};

function evRoll(e, car) {
  const s = (e.seed != null ? e.seed : (e.sc * 17.3 + e.t0 * 5.7)) * 9973 + car.mass * 13.7 + (car.blocks || 0) * 7.3 + (e.id || 1) * 31.1;
  return ((Math.sin(s) * 43758.5453123) % 1 + 1) % 1;
}

function simulate(car, laps, events) {
  events = events || [];
  const P = PHYS, G = P.G, m = car.mass / 1000;
  const Lc = COURSE.length, total = Lc * laps;
  const dt = 0.004, recEvery = 5, J = COURSE.F.jump, D2R = Math.PI / 180;
  const rec = { t: [], s: [], v: [], air: [], hop: [], pitch: [], tip: [], geff: [] };
  const stats = { topV: 0, maxTip: 0, minG: 9, jump: null, waveHop: 0 };
  let s = 0, v = 0, t = 0, step = 0, hop = 0, pitch = 0;
  let tipT = 0, liftT = 0, waveT = 0, jumpedLap = -1, air = null, fail = null, finish = null;
  let tipRatio = 0, geffNow = G, stunT = 0, blownT = 0, shortT = 0, lowT = 0, magLoss = 0, fanLoss = 0, barInfo = null;
  const hitBar = {};
  const Lm = 0.6 * ((car.mUser || 0) / 45) + 0.4 * ((car.blocks || 0) / 120);
  const ironMass = car.ironMass != null ? car.ironMass : (car.mUser || 0);
  const push = () => {
    rec.t.push(t); rec.s.push(s); rec.v.push(v); rec.air.push(air ? 1 : 0);
    rec.hop.push(hop); rec.pitch.push(pitch); rec.tip.push(tipRatio); rec.geff.push(geffNow / G);
  };
  push();
  while (t < 90 && !fail && finish === null) {
    const lap = Math.floor(s / Lc), sl = s - lap * Lc;
    const q = 0.6 * v * v;
    const Flift = P.KL * q * car.Fy, Fdrag = P.KD * q * car.D;
    geffNow = G - Flift / m;
    if (v > 2 && geffNow / G < stats.minG) stats.minG = geffNow / G;

    if (air) {
      const tau = t - air.t0;
      s = air.s0 + air.vx * tau; v = air.vx;
      hop = Math.max(0, air.vy * tau - 0.5 * air.g * tau * tau);
      pitch = air.th0 + 0.5 * air.acc * tau * tau / D2R;
      t += dt;
      if (tau >= air.tf) {
        if (air.outcome) fail = { reason: air.outcome, s, t, info: { d: air.d, theta: air.theta, land: J.landLen, geff: air.g / G } };
        else { v = air.vx * 0.96; hop = 0; pitch = 0; air = null; }
      }
    } else {
      const lip = J.s0 + J.rampLen;
      if (sl >= lip && sl < lip + 0.4 && jumpedLap !== lap) {
        jumpedLap = lap;
        const al = J.ang * D2R, vx = v * Math.cos(al), vy = v * Math.sin(al);
        const g = Math.max(geffNow, 0.5 * G), tf = 2 * vy / g, d = vx * tf;
        const Mn = P.KL * q * car.M * 0.005, I_ = m * P.K_GYR * P.K_GYR, acc = Mn / I_;
        const th0 = al / D2R * 0.25 - 18 * car.cgBias;
        const theta = th0 + 0.5 * acc * tf * tf / D2R;
        let outcome = null;
        if (d > J.gap + J.landLen - 0.1) outcome = 'over';
        else if (theta > 26) outcome = 'flipback';
        else if (theta < -26) outcome = 'flipfront';
        air = { t0: t, tf, d, vx, vy, g, acc, th0, theta, outcome, s0: s };
        if (!stats.jump || d > stats.jump.d) stats.jump = { d, theta, tf, v, g: g / G };
        continue;
      }
      if (geffNow < 0.68 * G && v > 2.5) liftT += dt; else liftT = Math.max(0, liftT - dt);
      if (liftT > 0.25) { fail = { reason: 'lift', s, t, info: { geff: geffNow / G, v } }; break; }
      let aFan = 0, aMag = 0, evAct = false, fanKoEv = null, magKoEv = null;
      for (const e of events) {
        if (e.kind === 'bar' || t < e.t0 || t >= e.t1) continue;
        let dd = Math.abs(sl - e.sc); dd = Math.min(dd, Lc - dd); if (dd > e.r) continue;
        evAct = true;
        if (e.kind === 'fan') {
          const wf = P.FAN_A * Math.pow(0.092 / m, P.FAN_WEIGHT) * (0.75 + 0.25 * clamp(car.D / 12, 0.5, 1.6));
          aFan = Math.max(aFan, wf);
          if ((car.mass <= 80 || (car.mass <= 88 && geffNow < 0.85 * G)) && evRoll(e, car) < P.ITEM_KO_PROB) fanKoEv = e;
        } else if (e.kind === 'mag') {
          aMag = Math.max(aMag, P.MAG_A * Lm * Lm);
          if (ironMass >= 32 && Lm >= 0.78 && evRoll(e, car) < P.ITEM_KO_PROB) magKoEv = e;
        }
      }
      if (fanKoEv && v > 1.2) {
        blownT += dt;
        if (blownT > 0.15) { fail = { reason: 'blown', s, t, info: { aw: aFan, ratio: aFan / P.FAN_A, dir: fanKoEv.dir || 1, v } }; break; }
      } else blownT = Math.max(0, blownT - dt);
      if (magKoEv) {
        shortT += dt;
        if (shortT > 0.15) { fail = { reason: 'short', s, t, info: { iron: ironMass, mass: car.mass, v } }; break; }
      } else shortT = Math.max(0, shortT - dt);
      const N_ = m * Math.max(geffNow, 0.2 * G);
      let Ft = Math.min(P.F0 * (1 - v / P.V0), P.MU_T * N_); if (Ft < 0) Ft = 0;
      const ks = COURSE.kappa(sl), kap = Math.abs(ks);
      const alat = v * v * kap;
      const Fw = P.WALL_MU * Math.max(0, m * alat - P.MU_L * N_);
      const dOut = (ks >= 0 ? 1 : -1) * (car.cgzOff || 0);
      const half = Math.max(0.012, P.HALF_TRACK - dOut);
      const yawF = 1 - 0.12 * clamp(car.yawStab || 0, -1, 1);
      tipRatio = alat * car.hcg / (half * Math.max(geffNow, 0.2 * G)) * yawF;
      if (tipRatio > stats.maxTip) stats.maxTip = tipRatio;
      if (tipRatio > 1) tipT += dt; else tipT = Math.max(0, tipT - dt * 2);
      if (tipT > 0.06) { fail = { reason: COURSE.inLane(sl) ? 'lane' : 'tip', s, t, info: { tip: tipRatio, v, kap, geff: geffNow / G, side: ks >= 0 ? 'right' : 'left' } }; break; }
      let a = (Ft - Fdrag - P.CRR * N_ - Fw) / m - G * Math.sin(COURSE.phi(sl)) - aMag - aFan; magLoss += aMag * dt; fanLoss += aFan * dt;
      if (stunT > 0) { a -= P.BAR_BRAKE; stunT -= dt; }
      hop = 0;
      const wv = COURSE.waveAt(sl);
      if (wv) {
        const vy = wv.amp * 2 * Math.PI / wv.lam * v;
        const hb = vy * vy / (2 * Math.max(geffNow, 0.3 * G));
        hop = Math.min(hb, 0.08);
        if (hb > stats.waveHop) stats.waveHop = hb;
        a -= 5.0 * Math.min(hb / wv.limit, 1.6);
        if (hb > wv.limit) waveT += dt; else waveT = Math.max(0, waveT - dt);
        if (waveT > 0.1) { fail = { reason: 'wave', s, t, info: { hb, limit: wv.limit, v, geff: geffNow / G } }; break; }
      }
      pitch = clamp((a / G) * 2.0, -4, 8);
      v += a * dt; if (v < 0) v = 0;
      s += v * dt; t += dt;
      if (v > stats.topV) stats.topV = v;
      for (const e of events) if (e.kind === 'bar' && t >= e.t0 && t < e.t1 && !hitBar[e.id]) {
        const st = e.sc + Math.floor((s - v * dt - e.sc) / Lc + 1) * Lc;
        if (s - v * dt < st && s >= st) {
          hitBar[e.id] = 1; const nose = car.nose == null ? 0.3 : car.nose, v0 = v;
          if (nose < P.BAR_FLIP && v > 2.0 && evRoll(e, car) < P.ITEM_KO_PROB) { fail = { reason: 'barricade', s, t, info: { nose, v } }; break; }
          const loss = Math.pow(1 - nose, P.BAR_EXP); v *= 1 - P.BAR_LOSS * loss; stunT = P.BAR_STUN * Math.max(0, loss - 0.3); barInfo = { nose, vLoss: v0 - v, v0 };
        }
      }
      if (fail) break;
      if (v < 0.15 && t > 2 && !evAct) lowT += dt; else lowT = 0;
      if (lowT > 0.4) { fail = { reason: 'stall', s, t, info: {} }; break; }
    }
    step++;
    if (step % recEvery === 0) push();
    if (s >= total) finish = t - (s - total) / Math.max(v, 0.1);
  }
  if (finish === null && !fail) fail = { reason: 'stall', s, t, info: {} };
  push();
  if (events.length) {
    const e = events[events.length - 1];
    stats.item = { kind: e.kind, hit: e.kind === 'fan' ? fanLoss > 0 : e.kind === 'mag' ? magLoss > 0 : !!barInfo, ratio: fanLoss, loss: magLoss, L: Lm, bar: barInfo };
  }
  return { rec, finish, dnf: fail, stats, total, laps, car };
}

function itemRisk(an) {
  const P = PHYS, m = an.mass / 1000, q = 0.6 * 16, geff = P.G - P.KL * q * an.Fy / m;
  const aw = P.FAN_A * Math.sqrt(Math.max(an.sideArea, 20) / 100) * Math.pow(0.09 / m, P.FAN_WEIGHT);
  return { fan: aw / (P.FAN_BLOW * Math.max(geff, 0.2 * P.G)), mag: 0.6 * (an.mUser / 45) + 0.4 * (an.blocks / 120), bar: an.nose };
}
const carParams = an => ({ mass: an.mass, D: an.D, Fy: an.Fy, M: an.M, hcg: an.hcg, cgBias: an.cgBias, cgzOff: an.cgzOff, yawStab: an.yawStab, Aside: an.sideArea, mUser: an.mUser, ironMass: (an.counts ? an.counts[3] : 0) * MASS_G[3], blocks: an.blocks, nose: an.nose });

const newGrid = () => new Uint8Array(N);
function put(g, x, y, z, m) { if (inGrid(x, y, z) && !isLocked(x, y, z)) g[I(x, y, z)] = m; }
function box(g, x0, y0, z0, x1, y1, z1, m) {
  for (let z = z0; z <= z1; z++) for (let y = y0; y <= y1; y++) for (let x = x0; x <= x1; x++) put(g, x, y, z, m);
}
function line2(cb, a0, b0, a1, b1) {
  let dx = Math.abs(a1 - a0), dy = -Math.abs(b1 - b0), sx = a0 < a1 ? 1 : -1, sy = b0 < b1 ? 1 : -1, e = dx + dy;
  for (;;) {
    cb(a0, b0);
    if (a0 === a1 && b0 === b1) break;
    const e2 = 2 * e; if (e2 >= dy) { e += dy; a0 += sx; } if (e2 <= dx) { e += dx; b0 += sy; }
  }
}
function slant(g, xa, ya, xb, yb, z0, z1, m) { line2((x, y) => { for (let z = z0; z <= z1; z++) put(g, x, y, z, m); }, xa, ya, xb, yb); }

const api = { itemRisk, carParams, floaters, isHalf, halfOpen, SHAPES, SHAPE_TYPES, SHAPE_COUNT, shapeCode, newShapes, NX, NY, NZ, CX, CY, CZ, BS, ZC, BZC, CELL_MM, WHEEL_Z, WHEEL_W, expand, M_BODY, M_WING, M_WEIGHT, L_AXLE, L_FLOOR, L_CHASSIS, L_WHEEL, MASS_G, BASE_MASS, LIM, WHEELS,
  BASE_CGX, BASE_CGY, N, I, LOCK, inGrid, isLocked, isFrame, analyze, COURSE, PHYS, simulate, newGrid, put, box, slant, line2, clamp };
if (typeof module !== 'undefined' && module.exports) module.exports = api; else root.TE = api;
})(typeof window !== 'undefined' ? window : globalThis);

/* プリセット車体 (サンプル兼ライバル) */
(function (root) {
'use strict';
const T = (typeof module !== 'undefined' && module.exports) ? require('./core3d.js') : root.TE;
const B = T.M_BODY, W = T.M_WING, K = T.M_WEIGHT, bx = T.box, sl = T.slant;

function standard() {
  const g = T.newGrid();
  bx(g, 1, 1, 2, 14, 1, 7, B);
  bx(g, 4, 2, 3, 11, 2, 6, B);
  bx(g, 15, 1, 3, 15, 1, 6, B);
  sl(g, 0, 4, 3, 2, 1, 8, W);
  bx(g, 1, 2, 3, 1, 3, 6, B);
  return g;
}
function highWing() {
  const g = T.newGrid();
  bx(g, 1, 1, 2, 14, 1, 7, B);
  bx(g, 6, 2, 3, 9, 2, 6, B);
  bx(g, 15, 1, 3, 15, 1, 6, B);
  sl(g, 0, 4, 3, 3, 0, 9, W);
  sl(g, 0, 3, 3, 2, 0, 9, W);
  bx(g, 1, 2, 3, 1, 3, 6, B);
  return g;
}
function lowrider() {
  const g = T.newGrid();
  bx(g, 1, 1, 2, 14, 1, 7, B);
  bx(g, 5, 1, 3, 10, 1, 6, K);
  bx(g, 6, 2, 3, 9, 2, 6, B);
  bx(g, 15, 1, 3, 15, 1, 6, B);
  sl(g, 0, 3, 2, 2, 2, 7, W);
  bx(g, 1, 2, 3, 1, 2, 6, B);
  return g;
}
function rocket() {
  const g = T.newGrid();
  bx(g, 3, 1, 2, 11, 1, 7, B);
  bx(g, 5, 2, 3, 10, 2, 6, B);
  bx(g, 12, 1, 3, 13, 1, 6, B);
  [[14, 4, 5], [15, 4, 5]].forEach(([x, a, b]) => bx(g, x, 1, a, x, 1, b, B));
  sl(g, 0, 3, 2, 2, 2, 7, W);
  bx(g, 1, 2, 3, 1, 2, 6, B);
  bx(g, 2, 1, 3, 2, 1, 6, B);
  return g;
}
function tower() {
  const g = T.newGrid();
  bx(g, 4, 1, 2, 11, 4, 7, B);
  bx(g, 1, 1, 2, 3, 1, 7, B);
  bx(g, 12, 1, 2, 14, 1, 7, B);
  bx(g, 15, 1, 3, 15, 1, 6, B);
  return g;
}
function liftNose() {
  const g = T.newGrid();
  bx(g, 1, 1, 2, 14, 1, 7, B);
  bx(g, 4, 2, 3, 9, 2, 6, B);
  sl(g, 11, 2, 15, 4, 1, 8, W);
  bx(g, 11, 2, 3, 11, 2, 6, B);
  return g;
}
function feather() {
  const g = T.newGrid();
  bx(g, 1, 1, 1, 14, 1, 8, B);
  sl(g, 14, 1, 15, 2, 2, 7, W);
  return g;
}
function tank() {
  const g = T.newGrid();
  bx(g, 2, 1, 3, 13, 1, 6, K);
  bx(g, 1, 1, 2, 14, 1, 2, B); bx(g, 1, 1, 7, 14, 1, 7, B);
  bx(g, 5, 2, 3, 10, 2, 6, K);
  bx(g, 15, 1, 2, 15, 1, 7, B);
  return g;
}
function skeleton() {
  const g = T.newGrid();
  bx(g, 4, 2, 4, 11, 2, 5, K);
  return g;
}
function drill() {
  const g = T.newGrid(), s = T.newShapes();
  const tri = (nx, nz) => { for (let c = 0; c < T.SHAPES.length; c++) { const sh = T.SHAPES[c]; if (sh.type !== 'tri') continue; if (sh.faces.some(f => Math.abs(f.n[1]) < 0.01 && Math.sign(Math.round(f.n[0] * 10)) === nx && Math.sign(Math.round(f.n[2] * 10)) === nz)) return c; } return 0; };
  const put1 = (x, y, z, m, code) => { const k = T.I(x, y, z); g[k] = m; if (code) s[k] = code; };
  bx(g, 2, 1, 2, 11, 1, 7, B);
  bx(g, 4, 1, 3, 9, 1, 6, K);
  bx(g, 5, 2, 3, 9, 2, 6, B);
  bx(g, 12, 1, 2, 12, 1, 7, B);
  bx(g, 13, 1, 3, 13, 1, 6, B); put1(13, 1, 2, B, tri(1, -1)); put1(13, 1, 7, B, tri(1, 1));
  bx(g, 14, 1, 4, 14, 1, 5, B); put1(14, 1, 3, B, tri(1, -1)); put1(14, 1, 6, B, tri(1, 1));
  put1(15, 1, 4, B, tri(1, -1)); put1(15, 1, 5, B, tri(1, 1));
  return { g, s };
}
const empty = () => T.newGrid();

const LIST = [
  { id: 'std', name: 'スタンダード', note: '素直なバランス型', fn: standard },
  { id: 'wing', name: 'ハイウイング', note: '大型リアウイングで押さえつける', fn: highWing },
  { id: 'low', name: 'ローライダー', note: '底におもりを積んだ低重心', fn: lowrider },
  { id: 'rkt', name: 'ロケット', note: '軽量でとがったノーズ', fn: rocket },
  { id: 'twr', name: 'タワー', note: '背が高い。コーナーは曲がれる？', fn: tower },
  { id: 'lft', name: 'リフトノーズ', note: '前上がりの翼。浮きそう', fn: liftNose },
  { id: 'fth', name: 'フェザー', note: '広くて軽い板。風に乗りすぎ？', fn: feather },
  { id: 'tnk', name: '重戦車', note: '鉄をぎっしり。風に強いが磁石に弱い', fn: tank },
  { id: 'skl', name: 'スケルトン', note: '最小限の鉄だけ。磁石に強い', fn: skeleton },
  { id: 'drl', name: 'ドリル', note: 'くさびで先端を尖らせた。障害物に強い', fn: () => drill().g, sfn: () => drill().s },
  { id: 'clr', name: 'まっさら', note: 'シャーシだけの状態', fn: empty }
];
const api = { LIST };
if (typeof module !== 'undefined' && module.exports) module.exports = api; else root.TEP = api;
})(typeof window !== 'undefined' ? window : globalThis);

(function(){'use strict';
/* ===== 共通 ===== */
const T = window.TE, PRE = window.TEP.LIST;
const NX = T.NX, NY = T.NY, NZ = T.NZ, I3 = T.I, BS = T.BS, CX = T.CX, CY = T.CY, CZ = T.CZ;
const $ = id => document.getElementById(id);
const clamp = (x, a, b) => Math.max(a, Math.min(b, x));
const root = document.documentElement;
const HAS3 = typeof THREE !== 'undefined';
let TH = {};
function readTheme() {
  const cs = getComputedStyle(root), g = n => cs.getPropertyValue(n).trim();
  TH = { paper: g('--paper'), card: g('--card'), ink: g('--ink'), ink2: g('--ink2'), line: g('--line'), line2: g('--line2'),
    accent: g('--accent'), cool: g('--cool'), body: g('--body'), wing: g('--wing'), lead: g('--lead'), good: g('--good'),
    bad: g('--bad'), warn: g('--warn'), track: g('--track'), wall: g('--wall'), chassis: g('--chassis'), tire: g('--tire'),
    rim: g('--rim'), grass: g('--grass'), bg: g('--bg') };
  if (typeof onTheme === 'function') onTheme();
}
matchMedia('(prefers-color-scheme: dark)').addEventListener('change', readTheme);
new MutationObserver(readTheme).observe(root, { attributes: true, attributeFilter: ['data-theme'] });

let toastTimer = 0;
function toast(msg) {
  const el = $('toast'); el.textContent = msg; el.classList.add('on');
  clearTimeout(toastTimer); toastTimer = setTimeout(() => el.classList.remove('on'), 2400);
}

/* ===== サウンドエフェクト (Web Audio API シンセサイザー) ===== */
const SFX = (() => {
  let ac = null, noiseBuf = null, mNode = null;
  let enabled = true;
  try { const v = localStorage.getItem('te4wd.sfx'); if (v === '0') enabled = false; } catch (_) {}
  function ctx() {
    if (!enabled) return null;
    if (!ac) {
      const Ctx = window.AudioContext || window.webkitAudioContext;
      if (!Ctx) return null;
      ac = new Ctx();
    }
    if (ac.state === 'suspended') ac.resume().catch(() => {});
    return ac;
  }
  function getNoise(c) {
    if (noiseBuf) return noiseBuf;
    const len = c.sampleRate * 1.2;
    noiseBuf = c.createBuffer(1, len, c.sampleRate);
    const d = noiseBuf.getChannelData(0);
    for (let i = 0; i < len; i++) d[i] = Math.random() * 2 - 1;
    return noiseBuf;
  }
  function tone(type, f0, f1, dur, gainVal, delay = 0) {
    const c = ctx(); if (!c) return;
    const t0 = c.currentTime + delay, t1 = t0 + dur;
    const o = c.createOscillator(), g = c.createGain();
    o.type = type;
    o.frequency.setValueAtTime(f0, t0);
    if (f1 !== f0) o.frequency.exponentialRampToValueAtTime(Math.max(20, f1), t1);
    g.gain.setValueAtTime(0.0001, t0);
    g.gain.linearRampToValueAtTime(gainVal, t0 + Math.min(0.012, dur * 0.25));
    g.gain.exponentialRampToValueAtTime(0.0001, t1);
    o.connect(g); g.connect(c.destination);
    o.start(t0); o.stop(t1 + 0.01);
  }
  function noise(dur, gainVal, freq = 1000, q = 1, type = 'bandpass') {
    const c = ctx(); if (!c) return;
    const t0 = c.currentTime, t1 = t0 + dur;
    const src = c.createBufferSource(); src.buffer = getNoise(c);
    const flt = c.createBiquadFilter(); flt.type = type; flt.frequency.setValueAtTime(freq, t0); flt.Q.value = q;
    const g = c.createGain();
    g.gain.setValueAtTime(gainVal, t0);
    g.gain.exponentialRampToValueAtTime(0.0001, t1);
    src.connect(flt); flt.connect(g); g.connect(c.destination);
    src.start(t0); src.stop(t1 + 0.01);
    return { flt, g, t0, t1 };
  }
  function stopMotor() {
    if (!mNode) return;
    try { mNode.o1.stop(); mNode.o2.stop(); mNode.g.disconnect(); } catch (_) {}
    mNode = null;
  }
  return {
    get on() { return enabled; },
    setOn(v) {
      enabled = !!v;
      try { localStorage.setItem('te4wd.sfx', enabled ? '1' : '0'); } catch (_) {}
      if (!enabled) stopMotor();
      syncSndBtns();
      if (enabled) this.click();
    },
    click() { tone('triangle', 620, 880, 0.04, 0.07); },
    rotate() { tone('triangle', 500, 740, 0.055, 0.09); },
    place(mat) {
      if (mat === 3) {
        tone('triangle', 240, 140, 0.09, 0.16);
        tone('sine', 1280, 960, 0.07, 0.08);
      } else {
        tone('triangle', 360, 720, 0.065, 0.14);
        noise(0.025, 0.06, 2200, 2);
      }
    },
    breakBlock() {
      tone('sine', 420, 130, 0.08, 0.14);
      noise(0.045, 0.08, 1400, 1.2);
    },
    error() {
      tone('sawtooth', 160, 115, 0.12, 0.09);
    },
    count(lbl) {
      if (lbl === '3' || lbl === '2' || lbl === '1') {
        tone('sine', 523.25, 523.25, 0.13, 0.14);
        tone('triangle', 1046.5, 1046.5, 0.1, 0.05);
      } else if (lbl === 'GO!') {
        tone('sine', 1046.5, 1046.5, 0.36, 0.18);
        tone('triangle', 1318.5, 1318.5, 0.36, 0.12);
      }
    },
    jump() { tone('sine', 260, 620, 0.14, 0.1); },
    land() { tone('triangle', 170, 55, 0.09, 0.14); noise(0.04, 0.08, 600, 1, 'lowpass'); },
    item(kind) {
      if (kind === 'fan') {
        const n = noise(0.95, 0.16, 380, 2.2, 'bandpass');
        if (n) { n.flt.frequency.linearRampToValueAtTime(950, n.t0 + 0.4); n.flt.frequency.linearRampToValueAtTime(320, n.t1); }
      } else if (kind === 'mag') {
        tone('sawtooth', 640, 220, 0.45, 0.11);
        tone('sine', 320, 760, 0.45, 0.11, 0.08);
      } else {
        tone('square', 220, 90, 0.14, 0.14);
        noise(0.12, 0.16, 900, 1.5);
      }
    },
    crash() {
      tone('sawtooth', 150, 38, 0.32, 0.2);
      noise(0.35, 0.22, 850, 0.8, 'lowpass');
    },
    match() {
      tone('triangle', 659.25, 659.25, 0.11, 0.13, 0);
      tone('triangle', 880, 880, 0.22, 0.15, 0.11);
    },
    finish(win) {
      stopMotor();
      if (win) {
        [[523.25, 0, 0.11], [659.25, 0.11, 0.11], [783.99, 0.22, 0.11], [1046.5, 0.33, 0.38]].forEach(([f, d, l]) => tone('triangle', f, f, l, 0.16, d));
      } else {
        [[587.33, 0, 0.14], [440, 0.15, 0.28]].forEach(([f, d, l]) => tone('triangle', f, f, l, 0.13, d));
      }
    },
    motor(v, air, active) {
      if (!enabled || !active || v <= 0.05) { stopMotor(); return; }
      const c = ctx(); if (!c) return;
      if (!mNode) {
        const o1 = c.createOscillator(), o2 = c.createOscillator(), flt = c.createBiquadFilter(), g = c.createGain();
        o1.type = 'sawtooth'; o2.type = 'triangle';
        flt.type = 'lowpass'; flt.frequency.value = 650;
        g.gain.value = 0.001;
        o1.connect(flt); o2.connect(flt); flt.connect(g); g.connect(c.destination);
        o1.start(); o2.start();
        mNode = { o1, o2, flt, g };
      }
      const now = c.currentTime;
      const baseF = 95 + clamp(v, 0, 7) * 38 + (air ? 35 : 0);
      mNode.o1.frequency.setTargetAtTime(baseF, now, 0.04);
      mNode.o2.frequency.setTargetAtTime(baseF * 1.98, now, 0.04);
      mNode.flt.frequency.setTargetAtTime(420 + v * 90, now, 0.05);
      mNode.g.gain.setTargetAtTime(clamp(v / 5, 0.01, 1) * 0.045, now, 0.05);
    },
    stopMotor
  };
})();
function syncSndBtns() {
  document.querySelectorAll('.snd-btn').forEach(b => {
    b.setAttribute('aria-pressed', String(SFX.on));
    b.innerHTML = b.id === 'bSound' ? (SFX.on ? '🔊<span class="snd-l"> 音 ON</span>' : '🔇<span class="snd-l"> 音 OFF</span>') : (SFX.on ? '🔊' : '🔇');
    b.onclick = () => SFX.setOn(!SFX.on);
  });
}
syncSndBtns();
function fitCanvas(cv, w, h) {
  const dpr = Math.min(window.devicePixelRatio || 1, 2.5);
  cv.style.width = w + 'px'; cv.style.height = h + 'px';
  cv.width = Math.round(w * dpr); cv.height = Math.round(h * dpr);
  const ctx = cv.getContext('2d'); ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  return ctx;
}
function circle(ctx, x, y, r) { ctx.beginPath(); ctx.arc(x, y, r, 0, Math.PI * 2); ctx.fill(); }
function paintWheel(ctx, cx, cy, R, ang) {
  ctx.fillStyle = TH.tire; circle(ctx, cx, cy, R);
  ctx.fillStyle = TH.rim; circle(ctx, cx, cy, R * 0.58);
  ctx.strokeStyle = TH.tire; ctx.lineWidth = Math.max(1, R * 0.12); ctx.lineCap = 'round'; ctx.beginPath();
  for (let i = 0; i < 5; i++) { const a = ang + i * Math.PI * 2 / 5; ctx.moveTo(cx, cy); ctx.lineTo(cx + Math.cos(a) * R * 0.55, cy + Math.sin(a) * R * 0.55); }
  ctx.stroke(); ctx.fillStyle = TH.tire; circle(ctx, cx, cy, R * 0.16);
}
/* 36色の固定パレット（1〜36: プリセット色, 0: 素材の標準色） */
const PALETTE = [
  // ビビッド＆レーシング (12)
  '#E52521', '#FF5500', '#FF9900', '#FFD000', '#88DD00', '#16A34A',
  '#0D9488', '#00A2FF', '#1D4ED8', '#6D28D9', '#C026D3', '#E11D48',
  // パステル＆ネオン・ライト (12)
  '#FF8A8A', '#FFB370', '#FFE670', '#C6F68D', '#6EE7B7', '#67E8F9',
  '#93C5FD', '#C4B5FD', '#F5D0FE', '#FDA4AF', '#39FF14', '#00FFFF',
  // ダーク＆メタリック・モノトーン (12)
  '#7F1D1D', '#7C2D12', '#713F12', '#14532D', '#1E3A8A', '#4C1D95',
  '#D4AF37', '#B45309', '#FFFFFF', '#CBD5E1', '#64748B', '#111827'
];
const newColors = () => new Uint8Array(T.N); // 0=標準色, 1..36=PALETTE[v-1]
const packCol = idx => idx | 0;
const colHex = v => (v >= 1 && v <= PALETTE.length) ? PALETTE[v - 1] : '#2F6FE0';
const matColor = m => (TH && (m === 3 ? TH.lead : TH.body)) || (m === 3 ? '#4a5160' : '#e8503a');
const cellColor = (m, cv) => (cv >= 1 && cv <= PALETTE.length) ? PALETTE[cv - 1] : matColor(m);

function paintSideThumb(ctx, g, ox, oy, cs, cc) {
  const H = NY;
  for (let y = 0; y < H; y++) for (let x = 0; x < NX; x++) {
    let m = 0, ch = false, cv = 0;
    for (let z = 0; z < NZ; z++) {
      const k = I3(x, y, z), u = g[k];
      if (u) { m = u; cv = cc ? cc[k] : 0; break; }
      if (T.LOCK[k] === T.L_CHASSIS) ch = true;
    }
    if (m) ctx.fillStyle = cellColor(m, cv); else if (ch) ctx.fillStyle = TH.chassis; else continue;
    ctx.fillRect(ox + x * cs - 0.2, oy + (H - 1 - y) * cs - 0.2, cs + 0.4, cs + 0.4);
  }
  for (const w of T.WHEELS) paintWheel(ctx, ox + w.cx / BS * cs, oy + (H - w.cy / BS) * cs, w.r / BS * cs, 0.4);
}

/* ===== ボクセルの3Dメッシュ ===== */
function solidVox(g, sg, x, y, z) {
  if (!T.inGrid(x, y, z)) return false;
  const k = I3(x, y, z); return (g[k] > 0 && !(sg && sg[k])) || T.LOCK[k] === T.L_CHASSIS || T.LOCK[k] === T.L_AXLE;
}
const SHADE = [[1, 0, 0], [-1, 0, 0], [0, 1, 0], [0, -1, 0], [0, 0, 1], [0, 0, -1]];
function buildCarGroup(g, opt) {
  opt = opt || {};
  const pos = [], col = [], idx = [], lines = [], sg = opt.s;
  const triData = [];
  const cBody = new THREE.Color(TH.body), cLead = new THREE.Color(TH.lead), cCh = new THREE.Color(TH.chassis), tmpC = new THREE.Color(), cc = opt.c;
  let vi = 0;
  const addFace = (poly, c, j, soft, voxelX, voxelY, voxelZ, faceNormal) => {
    for (const v of poly) { pos.push(v[0], v[1], v[2]); col.push(c.r * j, c.g * j, c.b * j); }
    for (let i = 1; i < poly.length - 1; i++) {
      idx.push(vi, vi + i, vi + i + 1);
      triData.push({ x: voxelX, y: voxelY, z: voxelZ, n: faceNormal });
    }
    if (opt.edges !== false && !soft) for (let e = 0; e < poly.length; e++) { const a = poly[e], b = poly[(e + 1) % poly.length]; lines.push(a[0], a[1], a[2], b[0], b[1], b[2]); }
    vi += poly.length;
  };
  for (let z = 0; z < NZ; z++) for (let y = 0; y < NY; y++) for (let x = 0; x < NX; x++) {
    const k = I3(x, y, z), u = g[k], lk = T.LOCK[k];
    let c;
    if (u > 0) { const cv = cc ? cc[k] : 0; if (cv) { tmpC.set(colHex(cv)); c = tmpC; } else c = u === 3 ? cLead : cBody; } else if (lk === T.L_CHASSIS || lk === T.L_AXLE) c = cCh; else continue;
    const j = 1 + (((x * 73856093) ^ (y * 19349663) ^ (z * 83492791)) & 15) / 15 * 0.07 - 0.035;
    const code = u > 0 && sg ? sg[k] : 0, shape = T.SHAPES[code];
    for (const f of shape.faces) {
      let skip = false;
      for (let a = 0; a < 3 && !skip; a++) {
        const v0 = f.v[0][a]; if ((v0 !== 0 && v0 !== 1) || !f.v.every(q => q[a] === v0)) continue;
        const d = [0, 0, 0]; d[a] = v0 === 1 ? 1 : -1;
        if (solidVox(g, sg, x + d[0], y + d[1], z + d[2])) skip = true;
      }
      if (skip) continue;
      addFace(f.v.map(v => [(x + v[0]) * BS, (y + v[1]) * BS, (z + v[2]) * BS]), c, j, f.soft, x, y, z, f.n);
    }
  }
  const geo = new THREE.BufferGeometry();
  geo.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3));
  geo.setAttribute('color', new THREE.Float32BufferAttribute(col, 3));
  geo.setIndex(idx); geo.computeVertexNormals();
  const grp = new THREE.Group();
  const mesh = new THREE.Mesh(geo, new THREE.MeshLambertMaterial({ vertexColors: true, side: THREE.DoubleSide }));
  mesh.userData = { triData };
  grp.add(mesh);
  if (opt.edges !== false && lines.length) {
    const lg = new THREE.BufferGeometry(); lg.setAttribute('position', new THREE.Float32BufferAttribute(lines, 3));
    grp.add(new THREE.LineSegments(lg, new THREE.LineBasicMaterial({ color: new THREE.Color(TH.ink), transparent: true, opacity: 0.28 })));
  }
  const wheels = [];
  const tireM = new THREE.MeshLambertMaterial({ color: new THREE.Color(TH.tire) }), rimM = new THREE.MeshLambertMaterial({ color: new THREE.Color(TH.rim) });
  for (const w of T.WHEELS) for (const zc of T.WHEEL_Z) {
    const wg = new THREE.Group();
    const t = new THREE.Mesh(new THREE.CylinderGeometry(w.r, w.r, T.WHEEL_W, 28), tireM); t.rotation.x = Math.PI / 2;
    const r = new THREE.Mesh(new THREE.CylinderGeometry(w.r * 0.58, w.r * 0.58, T.WHEEL_W + 0.06, 20), rimM); r.rotation.x = Math.PI / 2;
    const sp = new THREE.Mesh(new THREE.BoxGeometry(w.r * 1.1, 0.35, T.WHEEL_W + 0.1), tireM);
    const sp2 = sp.clone(); sp2.rotation.z = Math.PI / 2;
    wg.add(t, r, sp, sp2); wg.position.set(w.cx, w.cy, zc); grp.add(wg); wheels.push(wg);
  }
  grp.userData = { wheels, geo, bodyMesh: mesh };
  return grp;
}
function disposeGroup(grp) {
  grp.traverse(o => { if (o.geometry) o.geometry.dispose(); });
}

const _shapeGeo = {};
function shapeGeo(code) {
  if (_shapeGeo[code]) return _shapeGeo[code];
  const pos = [], idx = []; let vi = 0;
  for (const f of T.SHAPES[code].faces) { f.v.forEach(v => pos.push(v[0], v[1], v[2])); for (let i = 1; i < f.v.length - 1; i++) idx.push(vi, vi + i, vi + i + 1); vi += f.v.length; }
  const geo = new THREE.BufferGeometry(); geo.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3)); geo.setIndex(idx); geo.computeVertexNormals();
  return (_shapeGeo[code] = { fill: geo, edge: new THREE.EdgesGeometry(geo, 30) });
}
function drawShapeIcon(ctx, code, hex, S0) {
  ctx.clearRect(0, 0, S0, S0);
  const sc = S0 * 0.34, ox = S0 / 2, oy = S0 * 0.56;
  const P = v => [ox + (v[0] - v[2]) * 0.866 * sc, oy + ((v[0] + v[2] - 1) * 0.5 - (v[1] - 0.5)) * sc];
  const rgb = [1, 3, 5].map(i => parseInt(hex.slice(i, i + 2), 16)), shade = [0.8, 0.55, 1.0, 0.5, 0.65, 0.9];
  for (const f of T.SHAPES[code].faces) {
    if (f.n[0] + f.n[1] + f.n[2] <= 0.0001) continue;
    let best = 0, bd = -2; SHADE.forEach((d, i) => { const dd = f.n[0] * d[0] + f.n[1] * d[1] + f.n[2] * d[2]; if (dd > bd) { bd = dd; best = i; } });
    const k = shade[best];
    ctx.fillStyle = `rgb(${rgb.map(q => Math.min(255, Math.round(q * k))).join(',')})`; ctx.strokeStyle = f.soft ? ctx.fillStyle : 'rgba(0,0,0,.55)'; ctx.lineWidth = Math.max(1, S0 * 0.035); ctx.lineJoin = 'round';
    ctx.beginPath(); f.v.forEach((v, i) => { const q = P(v); i ? ctx.lineTo(q[0], q[1]) : ctx.moveTo(q[0], q[1]); }); ctx.closePath(); ctx.fill(); ctx.stroke();
  }
}

/* ===== エディタ状態 ===== */
let vReady = false;
const S = { g: T.newGrid(), c: newColors(), s: T.newShapes(), col: 0, mat: 1, slot: 0, lastBlock: 0,
  slots: [{ m: 1, col: 0, sh: 'cube', ori: 0 }, { m: 3, col: 0, sh: 'cube', ori: 0 }, { m: 1, col: 0, sh: 'half', ori: 0 }, { m: 1, col: 0, sh: 'tri', ori: 0 }, { m: 1, col: 0, sh: 'pyr', ori: 0 },
    { m: 1, col: 0, sh: 'cyl', ori: 0 }], sym: false,
  tunnel: true, an: null, undo: [], redo: [], dirty3: true, presetId: 'std' };
function onTheme() { renderHotbar(); S.dirty3 = true; applyTheme3d(); if (typeof R !== 'undefined') R.themeDirty = true; }
const markDirty = () => { S.dirty3 = true; };

const snap = () => ({ g: S.g.slice(), c: S.c.slice(), s: S.s.slice() });
const restore = sn => { S.g = sn.g; S.c = sn.c; S.s = sn.s; };
function updUndo() { $('bUndo').disabled = !S.undo.length; $('bRedo').disabled = !S.redo.length; }
function pushUndo(before) { S.undo.push(before || snap()); if (S.undo.length > 60) S.undo.shift(); S.redo.length = 0; updUndo(); }
function undo() { if (!S.undo.length) return; S.redo.push(snap()); restore(S.undo.pop()); changed(); updUndo(); SFX.click(); }
function redo() { if (!S.redo.length) return; S.undo.push(snap()); restore(S.redo.pop()); changed(); updUndo(); SFX.click(); }
$('bUndo').onclick = undo; $('bRedo').onclick = redo;
$('bClear').onclick = () => { pushUndo(); S.g = T.newGrid(); S.c = newColors(); S.s = T.newShapes(); S.presetId = null; changed(); SFX.breakBlock(); toast('ぜんぶ消しました（もどすで復活）'); };

const KD = T.PHYS.KD, KL = T.PHYS.KL, QREF = 0.6 * 16;
function changed() {
  planKey = '';
  S.ver = (S.ver || 0) + 1; S.an = T.analyze(S.g, S.s); updateSide(); markDirty(); updTabs();
}
function gauge(t, n, bar, h) { return `<div class="gg"><span class="t">${t}</span><span class="n">${n}</span><span class="bar">${bar}</span><span class="h">${h}</span></div>`; }
function updateSide() {
  const a = S.an, L = T.LIM;
  const lo = 50, hi = 160, pct = v => clamp((v - lo) / (hi - lo), 0, 1) * 100;
  $('wzone').style.left = pct(L.minW) + '%'; $('wzone').style.width = (pct(L.maxW) - pct(L.minW)) + '%';
  $('wfill').style.width = pct(a.mass) + '%'; $('wlbl').textContent = a.mass.toFixed(1) + ' g';
  const okW = a.rules.weightMin && a.rules.weightMax;
  $('wfill').style.background = okW ? 'var(--ink)' : 'var(--bad)';
  if ($('inspectTag')) {
    const ok = okW && a.rules.connected;
    $('inspectTag').textContent = `${a.mass.toFixed(0)}g ${ok ? '○' : '×'}`;
    $('inspectTag').style.background = ok ? 'var(--good)' : 'var(--bad)';
  }
  const row = (ok, name, val) => `<li class="${ok ? 'ok' : 'ng'}"><span class="mk">${ok ? '○' : '×'}</span><span class="nm">${name}</span><span class="nv">${val}</span></li>`;
  const wmsg = a.mass < L.minW ? `あと ${(L.minW - a.mass).toFixed(1)}g 足りない` : a.mass > L.maxW ? `${(a.mass - L.maxW).toFixed(1)}g 重すぎ` : a.mass.toFixed(1) + 'g';
  $('checks').innerHTML =
    row(okW, `重量 ${L.minW}〜${L.maxW}g`, wmsg) +
    row(true, '全長 160mm以内', a.dims.len + 'mm') +
    row(true, '全幅 100mm以内', a.dims.wid + 'mm') +
    row(true, '全高 60mm以内', a.dims.hgt + 'mm') +
    row(a.rules.connected, 'パーツのつながり', a.rules.connected ? '全部つながっている' : a.floatCells.length + 'ブロック浮いている') +
    row(true, '車輪をつなぐフレーム', '全車共通・消せない');
  const q = QREF, m = a.mass / 1000;
  const dragGf = KD * q * a.D / 9.8 * 1000;
  const dfRatio = -KL * q * a.Fy / (m * 9.8), geff = 1 + dfRatio;
  const centered = (v, max, cPos, cNeg) => {
    const w = clamp(Math.abs(v) / max, 0, 1) * 50;
    return `<i style="left:49.5%;width:3px;background:var(--line2)"></i>` + (v >= 0 ? `<i style="left:50%;width:${w}%;background:${cPos}"></i>` : `<i style="left:${50 - w}%;width:${w}%;background:${cNeg}"></i>`);
  };
  const zoff = (a.cgz - T.ZC) * 5;
  $('gauges').innerHTML =
    gauge('空気抵抗', Math.round(dragGf) + ' gf', `<i style="left:0;width:${clamp(a.D / 26, 0, 1) * 100}%;background:var(--accent)"></i>`, 'とがった形ほど小さい。') +
    gauge('接地の強さ', geff.toFixed(2) + ' G', `<i style="left:0;width:${clamp(geff / 1.6, 0, 1) * 100}%;background:${geff < 0.75 ? 'var(--bad)' : 'var(--cool)'}"></i>`, geff < 0.75 ? '浮きすぎ。このままだとコースアウトします。' : '0.7G を下回ると浮いてコースアウト。軽い車ほど落ちやすい。') +
    gauge(dfRatio >= 0 ? 'ダウンフォース' : '浮く力', (dfRatio >= 0 ? '+' : '−') + Math.abs(Math.round(dfRatio * 100)) + '% 車重', centered(dfRatio, 0.6, 'var(--cool)', 'var(--bad)'), '後ろ上がりの板は押さえつけ、前上がりの板や広い天井は浮かせます。') +
    gauge('先端の尖り', Math.round(a.nose * 100) + '%', `<i style="left:0;width:${a.nose * 100}%;background:var(--accent)"></i>`, '前に四角錐・くさび・斜めの面があるほど高い。バリケードに強い。平ら・丸い先端は0に近い。') +
    gauge('重心の高さ', (a.cgy * 5).toFixed(1) + ' mm', `<i style="left:0;width:${clamp((a.cgy - 2) / 4, 0, 1) * 100}%;background:var(--ink)"></i>`, '低いほどコーナーで横転しにくい。') +
    gauge('前後バランス', (a.cgBias >= 0 ? '前 ' : '後ろ ') + Math.abs(a.cgBias * 100).toFixed(0) + '%', centered(a.cgBias * 100, 25, 'var(--ink)', 'var(--ink)'), '前寄りだとジャンプで前のめりに。') +
    gauge('左右バランス', (zoff >= 0 ? '右 ' : '左 ') + Math.abs(zoff).toFixed(1) + ' mm', centered(zoff, 10, 'var(--ink)', 'var(--ink)'), 'ずれていると片側のコーナーで横転しやすい。') +
    gauge('ヨー安定', a.yawStab >= 0 ? '直進しやすい' : '尻を振りやすい', centered(a.yawStab, 1, 'var(--good)', 'var(--bad)'), '上から見て、風を受ける面が重心より後ろにあると安定。') +
    gauge('空気の回す力', a.M >= 0 ? '機首上げ' : '機首下げ', centered(a.M, 40, 'var(--accent)', 'var(--cool)'), 'ジャンプ中に機首を上げ下げする向きの力。');
  const ok = a.rules.ok;
  $('goRace').classList.toggle('ng', !ok);
  $('goRace').disabled = false;
  const why = !a.rules.weightMin ? `車重不足（${a.mass.toFixed(1)}g / 70g以上必要）` : !a.rules.weightMax ? `重量オーバー（${a.mass.toFixed(1)}g / 140g以下必要）` : !a.rules.connected ? `浮きブロックあり（${a.floatCells.length}個）` : '車検OK。サーキットへ。';
  $('goHint').textContent = why; $('goHint').style.color = ok ? 'var(--good)' : 'var(--bad)';
}

const idx = (x, y, z) => I3(x, y, z);
const cur = () => ({ g: S.g, c: S.c, s: S.s });
const MAT_NAME = { 1: 'プラスチック', 3: '鉄' };

const curSlot = () => S.slots[S.slot];
const slotCode = sl => T.shapeCode(sl.sh || 'cube', sl.ori || 0);
const placeSlot = () => curSlot();
const slotHex = sl => sl.col ? colHex(sl.col) : matColor(sl.m || 1);
const popcnt = n => { let c = 0; while (n) { c += n & 1; n >>= 1; } return c; };
function slotName(sl) {
  return MAT_NAME[sl.m] + 'の' + T.SHAPE_TYPES.find(t => t.id === (sl.sh || 'cube')).name + (sl.col ? `（色#${sl.col}）` : '（標準色）');
}
function slotIcon(cv, sl, size) {
  const ctx = fitCanvas(cv, size, size);
  drawShapeIcon(ctx, slotCode(sl), slotHex(sl), size);
}
function renderHotbar() {
  const box = $('hotbar'); if (!box) return;
  if (!box.children.length) for (let i = 0; i < S.slots.length; i++) {
    const b = document.createElement('button'); b.className = 'hb'; b.innerHTML = '<canvas></canvas><span class="hn"></span>';
    b.onclick = () => selectSlot(i, true); box.appendChild(b);
  }
  S.slots.forEach((sl, i) => {
    const b = box.children[i];
    b.setAttribute('aria-pressed', String(i === S.slot)); b.title = (i + 1) + ': ' + slotName(sl) + '（クリックで色・形を変更）'; b.setAttribute('aria-label', slotName(sl));
    b.querySelector('.hn').textContent = i + 1; slotIcon(b.querySelector('canvas'), sl, 40);
  });
}
function renderPop() {
  const sl = curSlot(), pop = $('pop'); if (!pop) return;
  $('popTitle').textContent = '向きと色（' + MAT_NAME[sl.m] + 'の' + T.SHAPE_TYPES.find(t => t.id === (sl.sh || 'cube')).name + '）';
  slotIcon($('popIcon'), sl, 56);
  const g = popcnt(T.SHAPES[slotCode(sl)].mask) * T.MASS_G[sl.m];
  $('popInfo').textContent = `${MAT_NAME[sl.m]} ・ 1個 ${g.toFixed(2)}g` + (sl.sh === 'cyl' ? '（重さ・空気の当たりは立方体と同じ）' : '');
  $('popRot').disabled = (sl.sh || 'cube') === 'cube';
  document.querySelectorAll('#swatches .swb').forEach(b => b.setAttribute('aria-pressed', String(+b.dataset.v === sl.col)));
}
function openPop(on) { const p = $('pop'); if (!p) return; p.hidden = !on; if (on) { renderPop(); openHelp(false); } }
function openHelp(on) {
  const p = $('helpPop'); if (!p) return;
  p.hidden = !on;
  const b = $('bHelp'); if (b) b.setAttribute('aria-expanded', String(on));
  if (on) openPop(false);
}
function syncS() { const sl = curSlot(); S.mat = sl.m; S.col = sl.col; }
function selectSlot(i, pop) {
  S.slot = i; S.lastBlock = i;
  syncS(); renderHotbar(); renderPop(); openPop(pop === true); S.dirty3 = true; if (vReady && V.ok) { showAim(V.lastE); SFX.click(); }
}
function editSlot(fn) { const sl = curSlot(); fn(sl); syncS(); renderHotbar(); renderPop(); SFX.click(); if (vReady && V.ok) showAim(V.lastE); }
function rotateSlot(dir) {
  const sl = placeSlot(); const n = T.SHAPE_COUNT[sl.sh || 'cube']; if (n < 2) { SFX.error(); toast('立方体は回しても同じ形です'); return; }
  sl.ori = ((sl.ori || 0) + dir + n) % n; syncS(); renderHotbar(); renderPop(); SFX.rotate(); if (vReady && V.ok) showAim(V.lastE);
}
(function buildPop() {
  const sw = $('swatches');
  const mk = (v, label, bg) => { const b = document.createElement('button'); b.className = 'swb'; b.dataset.v = v; b.title = label; b.setAttribute('aria-label', label); b.style.background = bg; b.onclick = () => editSlot(sl => { sl.col = v; }); sw.appendChild(b); };
  mk(0, '素材の標準色', 'linear-gradient(135deg,var(--body) 50%,var(--lead) 50%)');
  PALETTE.forEach((h, i) => mk(i + 1, `色 #${i + 1} (${h})`, h));
  $('popRot').onclick = () => rotateSlot(1);
  $('popClose').onclick = () => openPop(false);
  if ($('bHelp')) $('bHelp').onclick = () => { const p = $('helpPop'); openHelp(p ? p.hidden : true); };
  if ($('helpClose')) $('helpClose').onclick = () => openHelp(false);
  document.addEventListener('pointerdown', e => {
    const p = $('pop');
    if (!p.hidden && !p.contains(e.target) && !$('hotbar').contains(e.target)) openPop(false);
    const hp = $('helpPop'), hb = $('bHelp');
    if (hp && !hp.hidden && !hp.contains(e.target) && (!hb || !hb.contains(e.target))) openHelp(false);
  }, true);
})();
renderHotbar(); selectSlot(0, false);

function setSym(on) {
  S.sym = on; const b = $('symBtn'); if (b) b.setAttribute('aria-pressed', String(on));
  const v = $('symVal'); if (v) v.textContent = on ? 'ON' : 'OFF'; else if (b) b.textContent = (isMobileScreen() ? '対称 ' : '左右対称 ') + (on ? 'ON' : 'OFF');
  if (V.ok && V.fp) toast((isMobileScreen() ? '対称 ' : '左右対称 ') + (on ? 'ON' : 'OFF'));
}
$('symBtn').onclick = () => setSym(!S.sym);

document.addEventListener('keyup', e => V.keys.delete(e.key.toLowerCase()));
window.addEventListener('blur', () => V.keys.clear());
document.addEventListener('keydown', e => {
  if ($('garage').hidden) return;
  const tag = (e.target.tagName || '').toLowerCase(); if (tag === 'input' && e.target.type === 'text') return;
  const k = e.key.toLowerCase();
  if ((e.ctrlKey || e.metaKey) && k === 'z') { e.preventDefault(); e.shiftKey ? redo() : undo(); return; }
  if ((e.ctrlKey || e.metaKey) && k === 'y') { e.preventDefault(); redo(); return; }
  if (e.ctrlKey || e.metaKey || e.altKey) return;
  if (k.length === 1 && k >= '1' && k <= '6') selectSlot(+k - 1);
  else if (k === 'm') setSym(!S.sym);
  else if (k === 'escape') {
    const hp = $('helpPop');
    if (hp && !hp.hidden) { openHelp(false); return; }
    if (V.fp) toggleFP(false); else if (V.max) toggleMax(false);
  }
  else if (k === ' ' || k === 'shift') { V.keys.add(k); if (k === ' ' && (V.fp || V.max)) e.preventDefault(); }
  else if (k === 'r') rotateSlot(e.shiftKey ? -1 : 1);
  else if (k === 'c') openPop($('pop').hidden);
  else if (k === 'g') toggleFP(!V.fp);
  else if ('wasdqe'.includes(k) && k.length === 1) { V.keys.add(k); e.preventDefault(); }
});

/* ===== 3Dビュー ===== */
const V = { ok: false, theta: 0.75, phi: 1.0, dist: 62, target: null, car: null, arrows: null, ghost: null, plane: null, cg: null, pend: null, ptrs: new Map(), moved: false, pinch0: 0, down: null, keys: new Set(), joy: { x: 0, y: 0, my: 0 }, tap: 'place', touchMode: 'place', hit: null, fill: null, lastE: null, hold: null, aim: null, fp: false, max: false, tapEdit: false, pos: null, yaw: 0, pitch: 0, locked: false, noLock: false };
const cv3 = $('v3');
vReady = true;

try { V.tapEdit = localStorage.getItem('te4wd.tapEdit') === '1'; } catch (_) {}
const tapOn = () => V.fp && V.tapEdit && document.body.classList.contains('mob');
function hideAimFx() { if (!V.ok) return; V.hit.visible = V.hit2.visible = V.fill.visible = V.fill2.visible = V.ghost.visible = V.ghost2.visible = false; }
function updTouchUi() {
  const mob = document.body.classList.contains('mob');
  const ui = $('fpTouchUi'); if (ui) ui.classList.toggle('active', V.fp || mob);
  const w = $('v3wrap'); if (w) { w.classList.toggle('is-fp', !!V.fp); w.classList.toggle('tap-edit', !!V.tapEdit); }
  const cr = $('cross'); if (cr) cr.style.display = V.fp && !tapOn() ? 'block' : 'none';
  const mb = $('bMethBtn'), mt = $('bMethTap');
  if (mb) mb.setAttribute('aria-pressed', String(!V.tapEdit));
  if (mt) mt.setAttribute('aria-pressed', String(!!V.tapEdit));
  const tp = $('bTapPlace'), tb = $('bTapBreak');
  if (tp) tp.setAttribute('aria-pressed', String(V.touchMode !== 'break'));
  if (tb) tb.setAttribute('aria-pressed', String(V.touchMode === 'break'));
}
function setTapEdit(on) {
  if (V.tapEdit === on) return;
  V.tapEdit = on;
  try { localStorage.setItem('te4wd.tapEdit', on ? '1' : '0'); } catch (_) {}
  hideAimFx(); updTouchUi(); SFX.click();
  toast(on ? 'タップ操作：画面をタップした場所に置く／壊す（ドラッグで見回し）' : 'ボタン操作：中央の十字に合わせてボタンで置く／壊す');
}
function setTouchMode(m) {
  V.touchMode = m;
  const p = $('bModePlace'), b = $('bModeBreak');
  if (p && b) {
    p.classList.toggle('act', m === 'place'); p.setAttribute('aria-pressed', String(m === 'place'));
    b.classList.toggle('act', m === 'break'); b.setAttribute('aria-pressed', String(m === 'break'));
  }
  if (V.ok && V.lastE) showAim(V.lastE);
  updTouchUi(); SFX.click();
  if (m === 'break') toast('「壊す」：タップしたブロックを削除します');
  else toast('「置く」：タップした場所にブロックを置きます');
  updTip();
}
if ($('bModePlace')) $('bModePlace').onclick = () => setTouchMode('place');
if ($('bModeBreak')) $('bModeBreak').onclick = () => setTouchMode('break');
const tapBtn = (id, fn) => { const b = $(id); if (!b) return; b.addEventListener('pointerdown', e => e.stopPropagation()); b.onclick = e => { e.stopPropagation(); fn(); }; };
tapBtn('bMethBtn', () => setTapEdit(false));
tapBtn('bMethTap', () => setTapEdit(true));
tapBtn('bTapPlace', () => { if (V.touchMode !== 'place') setTouchMode('place'); });
tapBtn('bTapBreak', () => { if (V.touchMode !== 'break') setTouchMode('break'); });

function init3d() {
  if (!HAS3) return fail3d('3D表示ライブラリを読み込めませんでした。');
  try {
    V.r = new THREE.WebGLRenderer({ canvas: cv3, antialias: true });
  } catch (e) { return fail3d('このブラウザでは3D表示(WebGL)が使えないため、ガレージで機体を作れません。'); }
  V.r.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
  V.scene = new THREE.Scene(); V.cam = new THREE.PerspectiveCamera(40, 4 / 3, 0.5, 400);
  V.target = new THREE.Vector3(CX / 2, 3.5, CZ / 2);
  V.scene.add(new THREE.AmbientLight(0xffffff, 0.72));
  const dl = new THREE.DirectionalLight(0xffffff, 0.62); dl.position.set(-30, 70, 45); V.scene.add(dl);
  V.grid = new THREE.GridHelper(66, 66, 0x8899aa, 0x8899aa); V.grid.material.transparent = true; V.grid.material.opacity = 0.35; V.grid.position.set(CX / 2, -0.01, CZ / 2); V.scene.add(V.grid);
  const gb = new THREE.BoxGeometry(1.04, 1.04, 1.04);
  V.ghost = new THREE.LineSegments(new THREE.EdgesGeometry(gb), new THREE.LineBasicMaterial({ color: 0xff6a2b })); V.ghost.visible = false; V.scene.add(V.ghost);
  V.hit = new THREE.LineSegments(new THREE.EdgesGeometry(new THREE.BoxGeometry(1.06, 1.06, 1.06)), new THREE.LineBasicMaterial({ color: 0xffffff })); V.hit.visible = false; V.scene.add(V.hit);
  V.hit2 = V.hit.clone(); V.hit2.visible = false; V.scene.add(V.hit2); V.ghost2 = V.ghost.clone(); V.ghost2.visible = false; V.scene.add(V.ghost2);
  V.fill = new THREE.Mesh(new THREE.BoxGeometry(0.98, 0.98, 0.98), new THREE.MeshBasicMaterial({ color: 0xff6a2b, transparent: true, opacity: 0.45, depthWrite: false })); V.fill.visible = false; V.scene.add(V.fill);
  V.fill2 = new THREE.Mesh(V.fill.geometry, V.fill.material.clone()); V.fill2.visible = false; V.scene.add(V.fill2);
  V.cg = new THREE.Mesh(new THREE.SphereGeometry(0.7, 14, 10), new THREE.MeshBasicMaterial({ color: 0xff2255 })); V.scene.add(V.cg);
  V.arrows = new THREE.Group(); V.scene.add(V.arrows);
  [V.ghost, V.ghost2, V.hit, V.hit2, V.fill, V.fill2].forEach(m => { m.scale.setScalar(BS); m.userData = {}; });
  V.ok = true; layout3d(); applyTheme3d();
  const ins = $('inspect'), insHdr = $('inspectHdr'), insTgl = $('bInspectTgl');
  if (insHdr && ins) {
    insHdr.onclick = () => {
      ins.classList.toggle('collapsed-mobile');
      const open = !ins.classList.contains('collapsed-mobile');
      if (insTgl) {
        insTgl.textContent = open ? '閉じる ▴' : '詳細 ▾';
        insTgl.setAttribute('aria-expanded', String(open));
      }
    };
  }
  initVirtualPad();
}
function fail3d(msg) {
  const d = document.createElement('div'); d.className = 'nowebgl'; d.textContent = msg; cv3.parentElement.appendChild(d);
}
function applyTheme3d() {
  if (!V.ok) return; V.scene.background = new THREE.Color(TH.bg);
  V.grid.material.color.set(TH.line2); V.hit.material.color.set(TH.ink);
}
function layout3d() {
  if (!V.ok) return; const w = cv3.parentElement.clientWidth || 400, h = cv3.parentElement.clientHeight || 300;
  V.r.setSize(w, h, false); V.cam.aspect = w / h; V.cam.updateProjectionMatrix(); V.dirtyCam = true;
}
function placeCam() {
  if (V.fp) {
    if (!V.pos) return;
    V.cam.position.copy(V.pos);
    V.cam.rotation.order = 'YXZ';
    V.cam.rotation.set(V.pitch || 0, V.yaw || 0, 0);
    V.cam.updateMatrixWorld();
    return;
  }
  const sp = Math.sin(V.phi);
  V.cam.position.set(V.target.x + V.dist * sp * Math.cos(V.theta), V.target.y + V.dist * Math.cos(V.phi), V.target.z + V.dist * sp * Math.sin(V.theta));
  V.cam.lookAt(V.target);
}
const CAMS = { iso: [0.75, 1.0, 62], side: [Math.PI / 2, Math.PI / 2, 66], top: [Math.PI / 2, 0.02, 74], front: [0, Math.PI / 2, 60], rear: [Math.PI, Math.PI / 2, 60] };
document.querySelectorAll('#v3btns [data-cam]').forEach(b => b.onclick = () => {
  const c = CAMS[b.dataset.cam];
  if (!c) return;
  if (V.fp) {
    const dist = 15;
    const sp = Math.sin(c[1]);
    const offset = new THREE.Vector3(dist * sp * Math.cos(c[0]), Math.max(3.0, dist * Math.cos(c[1])), dist * sp * Math.sin(c[0]));
    V.pos = V.target.clone().add(offset);
    if (V.pos.y < 3.5) V.pos.y = 3.5;
    const d = new THREE.Vector3().subVectors(V.target, V.pos);
    V.yaw = Math.atan2(-d.x, -d.z);
    V.pitch = clamp(Math.asin(d.y / d.length()), -1.2, 1.2);
    placeCam();
  } else {
    V.theta = c[0]; V.phi = c[1]; V.dist = c[2];
  }
});

function rebuild3d() {
  if (!V.ok) return;
  if (V.car) { V.scene.remove(V.car); disposeGroup(V.car); }
  const PP = S.preview || cur(); V.car = buildCarGroup(PP.g, { c: PP.c, s: PP.s }); V.scene.add(V.car);
  const a = S.an;
  V.cg.position.set(a.cgx, a.cgy, a.cgz);
  S.dirty3 = false;
}
function updPlane() {}
function voxelRay(o, d) {
  const lo = [-1, -1, -1], hi = [NX + 1, NY + 1, NZ + 1], O = [o.x / BS, o.y / BS, o.z / BS], D = [d.x / BS, d.y / BS, d.z / BS];
  let t0 = 0, t1 = 1e9;
  for (let i = 0; i < 3; i++) {
    if (Math.abs(D[i]) < 1e-9) { if (O[i] < lo[i] || O[i] > hi[i]) return null; continue; }
    let a = (lo[i] - O[i]) / D[i], b = (hi[i] - O[i]) / D[i]; if (a > b) { const t = a; a = b; b = t; }
    t0 = Math.max(t0, a); t1 = Math.min(t1, b);
  }
  if (t0 > t1) return null;
  const P = O.map((v, i) => v + D[i] * (t0 + 1e-6));
  const c = P.map(v => Math.floor(v)).map((v, i) => clamp(v, -1, [NX, NY, NZ][i]));
  const step = D.map(v => v > 0 ? 1 : -1), tD = D.map(v => Math.abs(v) < 1e-9 ? 1e9 : Math.abs(1 / v));
  const tM = c.map((v, i) => Math.abs(D[i]) < 1e-9 ? 1e9 : ((step[i] > 0 ? v + 1 : v) - P[i]) / D[i] + t0);
  let prev = null, lastAx = -1, tEnter = t0;
  for (let n = 0; n < 220; n++) {
    if (c[0] < -1 || c[1] < -1 || c[2] < -1 || c[0] > NX || c[1] > NY || c[2] > NZ) return null;
    if (T.inGrid(c[0], c[1], c[2])) {
      const k = idx(c[0], c[1], c[2]), lk = T.LOCK[k];
      if (S.g[k] > 0 || lk === T.L_CHASSIS || lk === T.L_AXLE) {
        if (lastAx >= 0) {
          const nn = [0, 0, 0]; nn[lastAx] = -step[lastAx];
          return { hit: c.slice(), prev: prev ? prev.slice() : null, n: nn, p: P.map((v, i) => i === lastAx ? c[i] + (step[i] > 0 ? 0 : 1) : O[i] + D[i] * tEnter), dir: [D[0], D[2]] };
        }
      }
    }
    prev = c.slice();
    const ax = tM[0] < tM[1] ? (tM[0] < tM[2] ? 0 : 2) : (tM[1] < tM[2] ? 1 : 2);
    c[ax] += step[ax]; tM[ax] += tD[ax]; lastAx = ax; tEnter = tM[ax] - tD[ax];
  }
  return null;
}
function rayAt(e, useTap) {
  const r = cv3.getBoundingClientRect();
  let nx = 0, ny = 0;
  if (V.fp && !useTap) {
    const crossEl = $('cross');
    if (crossEl) {
      const cr = crossEl.getBoundingClientRect();
      const cx = cr.left + cr.width / 2;
      const cy = cr.top + cr.height / 2;
      nx = ((cx - r.left) / r.width) * 2 - 1;
      ny = -((cy - r.top) / r.height) * 2 + 1;
    }
  } else if (e && typeof e.clientX === 'number') {
    nx = ((e.clientX - r.left) / r.width) * 2 - 1;
    ny = -((e.clientY - r.top) / r.height) * 2 + 1;
  }
  const rc = new THREE.Raycaster();
  rc.setFromCamera({ x: nx, y: ny }, V.cam);

  if (V.car && V.car.userData && V.car.userData.bodyMesh) {
    const mesh = V.car.userData.bodyMesh;
    const triData = mesh.userData && mesh.userData.triData;
    const hits = rc.intersectObject(mesh, false);
    if (hits && hits.length > 0 && triData) {
      let hit = null, info = null;
      for (let i = 0; i < hits.length; i++) {
        const d = triData[hits[i].faceIndex];
        if (!d) continue;
        if (rc.ray.direction.x * d.n[0] + rc.ray.direction.y * d.n[1] + rc.ray.direction.z * d.n[2] < -1e-4) {
          hit = hits[i];
          info = d;
          break;
        }
      }
      if (!hit && hits.length > 0) {
        hit = hits[0];
        info = triData[hit.faceIndex];
      }
      if (info && T.inGrid(info.x, info.y, info.z)) {
        const c = [info.x, info.y, info.z];
        const fn = info.n;
        const nx_ = Math.abs(fn[0]), ny_ = Math.abs(fn[1]), nz_ = Math.abs(fn[2]);
        const ax = nx_ > ny_ ? (nx_ > nz_ ? 0 : 2) : (ny_ > nz_ ? 1 : 2);
        const nn = [0, 0, 0];
        nn[ax] = fn[ax] > 0 ? 1 : -1;
        const prev = [c[0] + nn[0], c[1] + nn[1], c[2] + nn[2]];
        return {
          hit: c,
          prev: prev,
          n: nn,
          p: [hit.point.x / BS, hit.point.y / BS, hit.point.z / BS],
          dir: [rc.ray.direction.x / BS, rc.ray.direction.z / BS]
        };
      }
    }
  }

  return voxelRay(rc.ray.origin, rc.ray.direction);
}
const REACH = 28;
function aim(e, useTap) {
  const h = rayAt(e, useTap); if (!h) return null;
  const hk = idx(...h.hit), p = h.prev;
  if (V.fp) {
    const cp = V.cam.position, dx = (h.hit[0] + 0.5) * BS - cp.x, dy = (h.hit[1] + 0.5) * BS - cp.y, dz = (h.hit[2] + 0.5) * BS - cp.z;
    const reach = useTap ? REACH * 2.2 : REACH;
    if (dx * dx + dy * dy + dz * dz > reach * reach) return null;
  }
  const lk = T.LOCK[hk];
  const sup = S.g[hk] > 0 || lk === T.L_CHASSIS || lk === T.L_AXLE;
  return {
    hit: h.hit, mine: S.g[hk] > 0, prev: p, n: h.n, fy: h.p[1] - h.hit[1], dir: h.dir, sup,
    put: sup && p && T.inGrid(...p) && !T.isLocked(...p) ? p : null
  };
}
const mirrorOf = c => (S.sym && c[2] !== NZ - 1 - c[2]) ? [c[0], c[1], NZ - 1 - c[2]] : null;
const codeFor = sl => slotCode(sl);
let planKey = '', planVal = null;
function planPlace(a) {
  if (!a || !a.sup) return null;
  const sl = placeSlot(), code = codeFor(sl, a);
  const key = [a.hit, a.prev, a.n, code, S.sym, S.ver, S.mat].join('|');
  if (key === planKey) return planVal;
  planKey = key; planVal = computePlan(a, code); return planVal;
}
function computePlan(a, code) {
  const mk = (hit, prev, n, cd) => {
    const hk = idx(...hit);
    if (S.g[hk] > 0 && T.isHalf(S.s[hk]) && T.isHalf(cd) && n && n.reduce((q, v, i) => q + v * T.halfOpen(S.s[hk])[i], 0) > 0) return { c: hit, code: 0, merge: true };
    if (prev && T.inGrid(...prev) && !T.isLocked(...prev) && S.g[idx(...prev)] === 0) return { c: prev, code: cd, merge: false };
    return null;
  };
  const g = S.g.slice(), s2 = S.s.slice(), items = [];
  const tryAdd = it => {
    if (!it) return false; const k = idx(...it.c), g0 = g[k], s0 = s2[k]; g[k] = S.mat; s2[k] = it.code;
    if (T.floaters(g, s2).includes(k)) { g[k] = g0; s2[k] = s0; return false; }
    items.push(it); return true;
  };
  if (!tryAdd(mk(a.hit, a.prev, a.n, code))) return null;
  if (S.sym) {
    const mz = c => c && [c[0], c[1], NZ - 1 - c[2]];
    if (NZ - 1 - a.hit[2] !== a.hit[2] || (a.prev && NZ - 1 - a.prev[2] !== a.prev[2]))
      tryAdd(mk(mz(a.hit), mz(a.prev), a.n && [a.n[0], a.n[1], -a.n[2]], T.SHAPES[code].mirror));
  }
  return items;
}
function pruneFloating() { const f = T.floaters(S.g, S.s); for (const k of f) { S.g[k] = 0; S.c[k] = 0; S.s[k] = 0; } return f.length; }
function showAim(e, useTap) {
  const a = V.ok && (V.fp || e) ? aim(e, useTap) : null; V.aim = a;
  const isBreak = V.touchMode === 'break';
  const ctr = (m, c) => { m.visible = !!c; if (c) m.position.set((c[0] + 0.5) * BS, (c[1] + 0.5) * BS, (c[2] + 0.5) * BS); };
  const org = (m, c, code) => { m.visible = !!c; if (c) { m.position.set(c[0] * BS, c[1] * BS, c[2] * BS); const g = shapeGeo(code); if (m.userData.code !== code) { m.userData.code = code; m.geometry = m.isLineSegments ? g.edge : g.fill; } } };
  const hitC = a && (isBreak ? a.mine : (a.mine || a.sup)) ? a.hit : null;
  ctr(V.hit, hitC); ctr(V.hit2, hitC && mirrorOf(hitC));
  if (V.hit.material) V.hit.material.color.set(isBreak ? 0xff2244 : 0xffffff);
  if (V.hit2.material) V.hit2.material.color.set(isBreak ? 0xff2244 : 0xffffff);
  if (isBreak) {
    V.fill.visible = V.fill2.visible = V.ghost.visible = V.ghost2.visible = false;
    return;
  }
  const plan = planPlace(a), p1 = plan && plan[0], p2 = plan && plan[1];
  org(V.fill, p1 && p1.c, p1 ? p1.code : 0); org(V.ghost, p1 && p1.c, p1 ? p1.code : 0);
  org(V.fill2, p2 && p2.c, p2 ? p2.code : 0); org(V.ghost2, p2 && p2.c, p2 ? p2.code : 0);
  if (p1) { const col = slotHex(placeSlot()); V.fill.material.color.set(col); V.fill2.material.color.set(col); }
}
function cells3d(c) {
  const out = [{ k: idx(c[0], c[1], c[2]), mir: false }];
  if (S.sym && NZ - 1 - c[2] !== c[2]) out.push({ k: idx(c[0], c[1], NZ - 1 - c[2]), mir: true });
  return out.filter(e => !T.LOCK[e.k]);
}
function act3d(kind, a) {
  if (!a) return false;
  if (kind === 'pick') return false;
  if (kind === 'place') {
    const plan = planPlace(a);
    if (!plan || !plan.length) {
      if (a.sup || a.mine) {
        SFX.error();
        if (!a.prev || !T.inGrid(...a.prev)) toast('そこには置けません（ブロックを置ける範囲の外です）');
        else if (T.isLocked(...a.prev)) {
          const lk = T.LOCK[idx(...a.prev)];
          if (lk === T.L_FLOOR) toast('そこには置けません（ブロックを置ける範囲の外です — 地面すれすれの段には置けません）');
          else if (lk === T.L_WHEEL) toast('そこには置けません（タイヤのまわりにはブロックを置けません）');
          else toast('そこには置けません（フレームの位置にはブロックを置けません）');
        } else {
          toast('そこには置けません（空中にはブロックを置けません。フレームかブロックにつなげてね）');
        }
      }
      return false;
    }
    for (const it of plan) { const k = idx(...it.c); S.g[k] = S.mat; S.c[k] = S.col; S.s[k] = it.code; }
    SFX.place(S.mat);
    return true;
  }
  if (!a.mine) return false;
  let did = false;
  for (const e of cells3d(a.hit)) {
    const k = e.k; if (!S.g[k]) continue;
    if (kind === 'break') { S.g[k] = 0; S.c[k] = 0; S.s[k] = 0; did = true; }
  }
  if (did && kind === 'break') {
    SFX.breakBlock();
    if (pruneFloating()) toast('つながりが切れたブロックも消えました');
  }
  return did;
}
function actionFor(d) {
  if (d.touch) return V.touchMode === 'break' ? 'break' : 'place';
  if (d.b === 2) return 'place';
  if (d.b === 1) return 'pick';
  return 'break';
}
function commit3d(kind, a) {
  const b4 = snap();
  if (!act3d(kind, a)) return false;
  if (kind !== 'pick') { pushUndo(b4); S.presetId = null; changed(); }
  return true;
}
function stopHold() {
  if (!V.hold) return;
  clearTimeout(V.hold.t); clearInterval(V.hold.i);
  if (V.hold.did) { pushUndo(V.hold.b4); S.presetId = null; changed(); }
  V.hold = null;
}
function startHold(kind) {
  const h = V.hold = { b4: snap(), did: false, t: 0, i: 0 };
  h.t = setTimeout(() => {
    const step = () => { showAim(V.lastE); if (act3d(kind, V.aim)) { h.did = true; S.an = T.analyze(S.g, S.s); markDirty(); } };
    if (V.down) V.down.rep = true;
    step(); h.i = setInterval(step, 110);
  }, 320);
}

/* ===== 一人称 ===== */
function lookBy(dx, dy) { V.yaw -= dx * 0.0025; V.pitch = clamp(V.pitch - dy * 0.0025, -1.5, 1.5); }
function tryLock() {
  try { const r = cv3.requestPointerLock && cv3.requestPointerLock(); if (r && r.catch) r.catch(() => { V.noLock = true; }); } catch (e) { V.noLock = true; }
  setTimeout(() => { if (!V.locked) V.noLock = true; updTip(); }, 700);
}
document.addEventListener('pointerlockchange', () => { V.locked = document.pointerLockElement === cv3; if (V.locked) V.noLock = false; else stopHold(); updTip(); });
document.addEventListener('pointerlockerror', () => { V.noLock = true; updTip(); });
function updTip() {
  const el = $('v3tip');
  if (el) el.textContent = '';
}
function toggleMax(on) {
  V.max = on; $('v3wrap').classList.toggle('max', on);
  const b = $('bMax');
  if (b) {
    b.innerHTML = on
      ? '<span class="lbl-max-pc">もどす</span><span class="lbl-max-sp">縮小</span>'
      : '<span class="lbl-max-pc">大きく</span><span class="lbl-max-sp">拡大</span>';
  }
  document.body.style.overflow = on ? 'hidden' : ''; layout3d();
}
const isMobileScreen = () => window.innerWidth <= 768 || (window.innerHeight <= 520 && window.innerWidth <= 920) || ('ontouchstart' in window && window.innerWidth <= 900);

function toggleFP(on) {
  if (!V.ok || V.fp === on) return;
  V.fp = on; V.keys.clear(); stopHold();
  V.cam.fov = on ? 75 : 40; V.cam.near = on ? 0.1 : 0.5; V.cam.updateProjectionMatrix();
  updTouchUi();
  $('bFP').textContent = on ? '全体視点' : '一人称'; $('bFP').setAttribute('aria-pressed', String(on));
  if (on) {
    if (!V.pos) {
      const sp0 = Math.sin(V.phi), o = new THREE.Vector3(sp0 * Math.cos(V.theta), Math.cos(V.phi), sp0 * Math.sin(V.theta));
      const portrait = cv3.clientHeight > cv3.clientWidth * 1.15;
      o.setLength(isMobileScreen() ? (portrait ? 40 : 26) : 16);
      V.pos = V.target.clone().add(o);
    }
    if (V.pos.y < 4.0) V.pos.y = 8;
    const d = new THREE.Vector3().subVectors(V.target, V.pos);
    V.yaw = Math.atan2(-d.x, -d.z); V.pitch = clamp(Math.asin(d.y / d.length()), -1.2, 1.2);
    placeCam();
    layout3d();
    if (!isMobileScreen()) toggleMax(true);
  } else {
    try { if (document.pointerLockElement) document.exitPointerLock(); } catch (e) {}
    V.hit.visible = V.hit2.visible = V.fill.visible = V.fill2.visible = V.ghost.visible = V.ghost2.visible = false;
    placeCam();
    layout3d();
    if (!isMobileScreen()) toggleMax(false);
  }
  updTip();
}
function moveFP(dt) {
  const hasKey = V.keys.size > 0;
  const hasJoy = V.joy && (V.joy.x !== 0 || V.joy.y !== 0 || V.joy.my !== 0);
  if (!hasKey && !hasJoy) return;
  const sp = 11 * dt, fx = -Math.sin(V.yaw), fz = -Math.cos(V.yaw), rx = Math.cos(V.yaw), rz = -Math.sin(V.yaw);
  let mx = 0, mz = 0, my = 0;
  if (V.keys.has('w')) { mx += fx; mz += fz; } if (V.keys.has('s')) { mx -= fx; mz -= fz; }
  if (V.keys.has('d')) { mx += rx; mz += rz; } if (V.keys.has('a')) { mx -= rx; mz -= rz; }
  if (V.keys.has(' ') || V.keys.has('e')) my += 1; if (V.keys.has('shift') || V.keys.has('q')) my -= 1;
  if (hasJoy) {
    if (V.joy.x || V.joy.y) {
      mx += rx * V.joy.x + fx * (-V.joy.y);
      mz += rz * V.joy.x + fz * (-V.joy.y);
    }
    if (V.joy.my) {
      my += V.joy.my;
    }
  }
  if (mx !== 0 || mz !== 0 || my !== 0) {
    V.pos.x = clamp(V.pos.x + mx * sp, -25, CX + 25);
    V.pos.z = clamp(V.pos.z + mz * sp, -25, CZ + 25);
    V.pos.y = clamp(V.pos.y + my * sp, 2.0, 40);
  }
}
function doPlaceFP() {
  placeCam();
  const a = aim(null);
  if (!a || !a.sup) { SFX.error(); toast('置く場所がありません（車体のブロックに向けてね）'); return; }
  if (!a.put) { SFX.error(); toast('ここには置けません'); return; }
  commit3d('place', a);
  if (S.dirty3) rebuild3d();
  showAim(null);
}
function doBreakFP() {
  placeCam();
  const a = aim(null);
  if (!a || !a.hit) { SFX.error(); toast('壊すブロックがありません（壊したいブロックに向けてね）'); return; }
  if (!a.mine) { SFX.error(); toast('基本パーツは壊せません'); return; }
  commit3d('break', a);
  if (S.dirty3) rebuild3d();
  showAim(null);
}
function setupRepeat(btn, action) {
  if (!btn) return;
  let timer = null, interval = null;
  const start = e => {
    e.preventDefault(); e.stopPropagation();
    try { btn.setPointerCapture(e.pointerId); } catch (_) {}
    action();
    timer = setTimeout(() => {
      interval = setInterval(action, 180);
    }, 350);
  };
  const stop = e => {
    if (e) { e.preventDefault(); e.stopPropagation(); }
    clearTimeout(timer); clearInterval(interval);
  };
  btn.addEventListener('pointerdown', start);
  btn.addEventListener('pointerup', stop);
  btn.addEventListener('pointercancel', stop);
  btn.addEventListener('contextmenu', e => e.preventDefault());
}
function initVirtualPad() {
  const pad = $('vPad'), stick = $('vStick');
  if (pad && stick) {
    let activePtr = null, centerX = 0, centerY = 0;
    const maxR = 28;
    const onDown = e => {
      e.preventDefault(); e.stopPropagation();
      activePtr = e.pointerId;
      try { pad.setPointerCapture(e.pointerId); } catch (_) {}
      const r = pad.getBoundingClientRect();
      centerX = r.left + r.width / 2;
      centerY = r.top + r.height / 2;
      update(e.clientX, e.clientY);
    };
    const onMove = e => {
      if (e.pointerId !== activePtr) return;
      e.preventDefault(); e.stopPropagation();
      update(e.clientX, e.clientY);
    };
    const onUp = e => {
      if (e.pointerId !== activePtr) return;
      e.preventDefault(); e.stopPropagation();
      activePtr = null;
      stick.style.transform = 'translate(0px, 0px)';
      V.joy.x = 0; V.joy.y = 0;
    };
    function update(cx, cy) {
      const dx = cx - centerX, dy = cy - centerY;
      const dist = Math.hypot(dx, dy);
      const r = Math.min(dist, maxR);
      const ang = dist > 0 ? Math.atan2(dy, dx) : 0;
      const kx = Math.cos(ang) * r, ky = Math.sin(ang) * r;
      stick.style.transform = `translate(${kx.toFixed(1)}px, ${ky.toFixed(1)}px)`;
      V.joy.x = kx / maxR;
      V.joy.y = ky / maxR;
    }
    pad.addEventListener('pointerdown', onDown);
    pad.addEventListener('pointermove', onMove);
    pad.addEventListener('pointerup', onUp);
    pad.addEventListener('pointercancel', onUp);
    pad.addEventListener('contextmenu', e => e.preventDefault());
  }
  const setupHold = (id, val) => {
    const b = $(id); if (!b) return;
    const s = e => { e.preventDefault(); e.stopPropagation(); try { b.setPointerCapture(e.pointerId); } catch (_) {} V.joy.my = val; b.classList.add('act'); };
    const e = ev => { if (ev) { ev.preventDefault(); ev.stopPropagation(); } V.joy.my = 0; b.classList.remove('act'); };
    b.addEventListener('pointerdown', s);
    b.addEventListener('pointerup', e);
    b.addEventListener('pointercancel', e);
    b.addEventListener('contextmenu', ev => ev.preventDefault());
  };
  setupHold('bFlyUp', 1);
  setupHold('bFlyDown', -1);
  setupRepeat($('bActPlace'), doPlaceFP);
  setupRepeat($('bActBreak'), doBreakFP);
}
$('bFP').onclick = () => toggleFP(!V.fp);
$('bMax').onclick = () => { if (V.fp) toggleFP(false); else toggleMax(!V.max); };

cv3.addEventListener('contextmenu', e => e.preventDefault());
cv3.addEventListener('auxclick', e => e.preventDefault());
cv3.addEventListener('pointerdown', e => {
  e.preventDefault();
  if (V.fp && !V.locked && !V.noLock && e.pointerType === 'mouse') { tryLock(); return; }
  try { cv3.setPointerCapture(e.pointerId); } catch (_) {}
  V.ptrs.set(e.pointerId, { x: e.clientX, y: e.clientY }); V.lastE = e;
  V.down = { x: e.clientX, y: e.clientY, b: e.button, touch: e.pointerType !== 'mouse', rep: false }; V.moved = false;
  if (V.ptrs.size === 2) { const [a, b] = [...V.ptrs.values()]; V.pinch0 = Math.hypot(a.x - b.x, a.y - b.y); V.moved = true; stopHold(); return; }
  const kind = actionFor(V.down);
  if (!V.fp && kind === 'break') startHold('break');
  else if (V.down.touch && tapOn()) showAim(e, true);
});
cv3.addEventListener('pointermove', e => {
  V.lastE = e;
  if (V.fp && V.locked) { lookBy(e.movementX || 0, e.movementY || 0); return; }
  const p = V.ptrs.get(e.pointerId);
  if (p) {
    const dx = e.clientX - p.x, dy = e.clientY - p.y; p.x = e.clientX; p.y = e.clientY;
    if (V.fp) {
      if (V.ptrs.size > 1 || (V.down && Math.hypot(e.clientX - V.down.x, e.clientY - V.down.y) > (V.down.touch ? 12 : 5))) {
        if (!V.moved && tapOn()) hideAimFx();
        V.moved = true;
      }
      lookBy(dx * 1.6, dy * 1.6);
      return;
    }
    if (V.ptrs.size === 2 && !V.fp) { const [a, b] = [...V.ptrs.values()]; const d = Math.hypot(a.x - b.x, a.y - b.y); if (V.pinch0) V.dist = clamp(V.dist * V.pinch0 / d, 22, 150); V.pinch0 = d; return; }
    if (V.down && !V.down.rep && (V.moved || Math.hypot(e.clientX - V.down.x, e.clientY - V.down.y) > (V.down.touch ? 15 : 5))) {
      V.moved = true; stopHold();
      V.theta -= dx * 0.008; V.phi = clamp(V.phi - dy * 0.008, 0.02, Math.PI - 0.05);
      V.hit.visible = V.hit2.visible = V.fill.visible = V.fill2.visible = V.ghost.visible = V.ghost2.visible = false; return;
    }
  }
  if (!V.ok || V.fp || (V.ptrs.size && V.moved)) return;
  showAim(e);
});
function up3d(e) {
  const had = V.ptrs.delete(e.pointerId), d = V.down;
  if (!had || !d) { if (!V.ptrs.size) V.down = null; stopHold(); return; }
  if (V.ptrs.size) return;
  V.down = null;
  const repeated = d.rep; stopHold();
  if (repeated || V.moved) return;
  const useTap = V.fp && d.touch && tapOn();
  if (V.fp && d.touch && !useTap) return;
  if (useTap) {
    const a = aim(e, true);
    if (!a || (V.touchMode === 'break' ? !a.mine : !a.sup)) { SFX.error(); toast(V.touchMode === 'break' ? '壊せるブロックがありません（自分で置いたブロックをタップしてね）' : '置く場所がありません（車体のブロックをタップしてね）'); }
    else { commit3d(actionFor(d), a); if (S.dirty3) rebuild3d(); }
    hideAimFx(); return;
  }
  commit3d(actionFor(d), aim(V.fp ? null : e)); showAim(V.fp ? null : e);
}
cv3.addEventListener('pointerup', up3d);
cv3.addEventListener('pointercancel', e => { V.ptrs.delete(e.pointerId); V.down = null; stopHold(); if (tapOn()) hideAimFx(); });
cv3.addEventListener('pointerleave', () => { if (!V.ptrs.size && !V.fp) V.hit.visible = V.hit2.visible = V.fill.visible = V.fill2.visible = V.ghost.visible = V.ghost2.visible = false; });
cv3.addEventListener('wheel', e => {
  e.preventDefault();
  if (V.fp) selectSlot((S.slot + (e.deltaY > 0 ? 1 : S.slots.length - 1)) % S.slots.length);
  else V.dist = clamp(V.dist * Math.exp(e.deltaY * 0.001), 22, 150);
}, { passive: false });
function moveCam(dt) {
  if (!V.keys.size) return;
  const sp = (V.dist * 0.5 + 8) * dt, fx = -Math.cos(V.theta), fz = -Math.sin(V.theta);
  let mx = 0, mz = 0, my = 0;
  if (V.keys.has('w')) { mx += fx; mz += fz; } if (V.keys.has('s')) { mx -= fx; mz -= fz; }
  if (V.keys.has('a')) { mx += fz; mz -= fx; } if (V.keys.has('d')) { mx -= fz; mz += fx; }
  if (V.keys.has('e') || V.keys.has(' ')) my += 1; if (V.keys.has('q') || V.keys.has('shift')) my -= 1;
  V.target.x = clamp(V.target.x + mx * sp, -4, CX + 4); V.target.z = clamp(V.target.z + mz * sp, -4, CZ + 4); V.target.y = clamp(V.target.y + my * sp, -1, CY + 4);
}

/* ===== サンプル / ガレージ ===== */
function loadPreset(p) { pushUndo(); S.g = p.fn(); S.c = newColors(); S.s = p.sfn ? p.sfn() : T.newShapes(); S.presetId = p.id; $('presetNote').textContent = p.name + '：' + p.note; changed(); }
const presetBox = $('presets');
PRE.forEach(p => { const b = document.createElement('button'); b.className = 'chip'; b.textContent = p.name; b.onclick = () => loadPreset(p); presetBox.appendChild(b); });

const SKEY = 'te4wd.v5.cars', OLDKEY = 'te4wd.v4.slots';
let carMem = null;
function readCars() {
  if (carMem) return carMem;
  try {
    const s = JSON.parse(localStorage.getItem(SKEY) || 'null'); if (Array.isArray(s)) return carMem = s;
    const old = JSON.parse(localStorage.getItem(OLDKEY) || 'null');
    if (Array.isArray(old)) return carMem = old.filter(Boolean);
  } catch (e) {}
  return carMem = [];
}
function writeCars(arr) { carMem = arr; try { localStorage.setItem(SKEY, JSON.stringify(arr)); } catch (e) {} }
function encodeGrid(g) {
  const out = []; let v = g[0], n = 0;
  for (let i = 0; i < g.length; i++) { if (g[i] === v) n++; else { out.push(v + ':' + n); v = g[i]; n = 1; } }
  out.push(v + ':' + n); return out.join(',');
}
function decodeGrid(s) {
  const g = T.newGrid(); let i = 0;
  for (const part of s.split(',')) { const [v, n] = part.split(':').map(Number); for (let k = 0; k < n && i < g.length; k++, i++) g[i] = v; }
  for (let k = 0; k < g.length; k++) { if (g[k] === 2) g[k] = 1; if (g[k] > 3 || T.LOCK[k]) g[k] = 0; }
  return g;
}
function decodeShapes(s, g) {
  const o = T.newShapes(); if (!s) return o; let i = 0;
  for (const part of s.split(',')) { const [v, n] = part.split(':').map(Number); for (let k = 0; k < n && i < o.length; k++, i++) o[i] = v < T.SHAPES.length ? v : 0; }
  for (let k = 0; k < o.length; k++) if (!g[k]) o[k] = 0;
  return o;
}
function decodeColors(s, g) {
  const c = newColors(); if (!s) return c; let i = 0;
  for (const part of s.split(',')) { const [v, n] = part.split(':').map(Number); for (let k = 0; k < n && i < c.length; k++, i++) c[i] = (v >= 1 && v <= PALETTE.length) ? v : 0; }
  for (let k = 0; k < c.length; k++) if (!g[k]) c[k] = 0;
  return c;
}
function saveCar() {
  const inp = $('carName'), name = (inp.value || '').trim().slice(0, 24);
  if (!name) { toast('機体の名前を入れてください'); inp.focus(); return; }
  const a = readCars().slice(), rec = { name, mass: Math.round(S.an.mass), g: encodeGrid(S.g), c: encodeGrid(S.c), s: encodeGrid(S.s) };
  const i = a.findIndex(x => x.name === name);
  if (i >= 0) a[i] = rec; else a.unshift(rec);
  writeCars(a); renderSlots(); toast(i >= 0 ? '「' + name + '」に上書き保存しました' : '「' + name + '」を保存しました');
}
/* 機体コード (VX6-...) の36色固定パレット超圧縮エンコード・デコード */
function bytesToB64Url(bytes) {
  let bin = ''; for (let i = 0; i < bytes.length; i++) bin += String.fromCharCode(bytes[i]);
  return btoa(bin).replace(/\+/g, '-').replace(/\//g, '_').replace(/=+$/, '');
}
function b64UrlToBytes(b64) {
  const s = b64.replace(/-/g, '+').replace(/_/g, '/');
  const bin = atob(s);
  const bytes = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) bytes[i] = bin.charCodeAt(i);
  return bytes;
}
function packCarBinary(rec) {
  const g = rec.gArr || decodeGrid(rec.g);
  const c = rec.cArr || decodeColors(rec.c, g);
  const s = rec.sArr || decodeShapes(rec.s, g);
  const nameBytes = new TextEncoder().encode((rec.name || 'マシン').slice(0, 24));
  const cells = [];
  for (let i = 0; i < T.N; i++) {
    if (T.LOCK[i]) continue;
    const m = g[i];
    if (!m) { cells.push(0); continue; }
    const ci = (c[i] >= 1 && c[i] <= PALETTE.length) ? c[i] : 0;
    const sh = s[i] || 0;
    cells.push((m === 3 ? 2 : 1) | (ci << 2) | (sh << 8));
  }
  const out = [nameBytes.length, ...nameBytes];
  let idx = 0;
  while (idx < cells.length) {
    const v = cells[idx]; let run = 1;
    while (idx + run < cells.length && cells[idx + run] === v && run < 127) run++;
    if (v === 0) {
      out.push(run - 1); // 0x00..0x7E: 空白の連続 (1..127個)
    } else {
      const mBit = (v & 3) === 2 ? 1 : 0, ci = (v >> 2) & 63, sh = (v >> 8) & 63;
      if (run === 1 && sh === 0) {
        out.push(0x80 | (mBit << 6) | ci); // 0x80..0xFF: 単発の立方体（素材1bit + 36色パレット6bit = 1バイト完結）
      } else if (sh === 0) {
        out.push(0x7F, (mBit << 6) | ci, run); // 立方体の連続 (3バイト)
      } else {
        out.push(0x7F, 0x80 | (mBit << 6) | ci, (sh << 2) | Math.min(run, 3)); // 回転・特殊形状パーツ
        if (run > 3) run = 3;
      }
    }
    idx += run;
  }
  return new Uint8Array(out);
}
function unpackCarBinary(bytes) {
  let p = 0;
  if (p >= bytes.length) return null;
  const nLen = bytes[p++];
  if (nLen > 96 || p + nLen > bytes.length) return null;
  const name = new TextDecoder().decode(bytes.subarray(p, p + nLen)) || 'ゲスト機体'; p += nLen;
  const g = T.newGrid(), c = newColors(), s = T.newShapes();
  const freeIdx = [];
  for (let i = 0; i < T.N; i++) if (!T.LOCK[i]) freeIdx.push(i);
  let k = 0;
  while (k < freeIdx.length && p < bytes.length) {
    const b = bytes[p++];
    if (b < 0x7F) {
      k += b + 1;
    } else if (b >= 0x80) {
      const m = (b & 0x40) ? 3 : 1, ci = b & 0x3F;
      const fi = freeIdx[k++]; g[fi] = m; s[fi] = 0; c[fi] = ci <= PALETTE.length ? ci : 0;
    } else {
      const b1 = bytes[p++], b2 = bytes[p++];
      const m = (b1 & 0x40) ? 3 : 1, ci = b1 & 0x3F;
      if ((b1 & 0x80) === 0) {
        const run = b2;
        for (let r = 0; r < run && k < freeIdx.length; r++, k++) {
          const fi = freeIdx[k]; g[fi] = m; s[fi] = 0; c[fi] = ci <= PALETTE.length ? ci : 0;
        }
      } else {
        const sh = (b2 >> 2) & 63, run = b2 & 3;
        for (let r = 0; r < run && k < freeIdx.length; r++, k++) {
          const fi = freeIdx[k]; g[fi] = m; s[fi] = sh < T.SHAPES.length ? sh : 0; c[fi] = ci <= PALETTE.length ? ci : 0;
        }
      }
    }
  }
  const an = T.analyze(g, s);
  return { name: name.slice(0, 24), mass: Math.round(an.mass), g: encodeGrid(g), c: encodeGrid(c), s: encodeGrid(s), gArr: g, cArr: c, sArr: s, an };
}
async function compressBytes(u8) {
  if (typeof CompressionStream === 'undefined') return null;
  try {
    const cs = new CompressionStream('deflate-raw');
    const w = cs.writable.getWriter(); w.write(u8); w.close();
    const buf = await new Response(cs.readable).arrayBuffer();
    return new Uint8Array(buf);
  } catch (_) { return null; }
}
async function decompressBytes(u8) {
  if (typeof DecompressionStream === 'undefined') return null;
  try {
    const ds = new DecompressionStream('deflate-raw');
    const w = ds.writable.getWriter(); w.write(u8); w.close();
    const buf = await new Response(ds.readable).arrayBuffer();
    return new Uint8Array(buf);
  } catch (_) { return null; }
}
async function exportCarCode(rec) {
  const raw = packCarBinary(rec);
  const comp = await compressBytes(raw);
  const best = (comp && comp.length < raw.length) ? comp : raw;
  const tag = (comp && comp.length < raw.length) ? 'VX6-' : 'VX6R-';
  return tag + bytesToB64Url(best);
}
async function importCarCode(codeStr) {
  if (!codeStr) return null;
  const str = String(codeStr).trim();
  const m = str.match(/VX6(R?)-[A-Za-z0-9_-]+/);
  if (!m) return null;
  const isRaw = m[1] === 'R';
  const body = m[0].replace(/^VX6R?-/, '');
  try {
    const bytes = b64UrlToBytes(body);
    const raw = isRaw ? bytes : await decompressBytes(bytes);
    return raw ? unpackCarBinary(raw) : null;
  } catch (e) { return null; }
}
async function copyText(txt, msg) {
  try {
    await navigator.clipboard.writeText(txt);
    toast((msg || 'コピーしました') + `（${txt.length}文字）`);
  } catch (_) {
    window.prompt(`以下の機体コード（${txt.length}文字）をコピーしてください:`, txt);
  }
}
function currentCarRec() {
  const nm = (($('carName') && $('carName').value) || '').trim() || 'マイマシン';
  return { name: nm, mass: Math.round(S.an.mass), g: encodeGrid(S.g), c: encodeGrid(S.c), s: encodeGrid(S.s), gArr: S.g, cArr: S.c, sArr: S.s };
}
function renderSlots() {
  const arr = readCars(), box = $('slots'); box.innerHTML = '';
  if (!arr.length) { box.innerHTML = '<p class="small" style="margin:0">まだ保存した機体はありません。名前を入れて「保存」を押してください。</p>'; return; }
  arr.forEach((s, i) => {
    const d = document.createElement('div'); d.className = 'slot full';
    const cv = document.createElement('canvas'); const W = 120, H = Math.round(W * (NY + 0.6) / NX); d.appendChild(cv);
    const ctx = fitCanvas(cv, W, H); ctx.clearRect(0, 0, W, H); const g = decodeGrid(s.g); paintSideThumb(ctx, g, 0, 0, W / NX, decodeColors(s.c, g));
    const nm = document.createElement('div'); nm.className = 'nm'; nm.textContent = s.name + (s.mass ? '（' + s.mass + 'g）' : ''); nm.title = s.name;
    const bt = document.createElement('div'); bt.className = 'bt';
    const ld = document.createElement('button'); ld.textContent = '読込';
    ld.onclick = () => { pushUndo(); S.g = decodeGrid(s.g); S.c = decodeColors(s.c, S.g); S.s = decodeShapes(s.s, S.g); S.presetId = null; $('carName').value = s.name; changed(); toast('「' + s.name + '」を読み込みました'); };
    const cp = document.createElement('button'); cp.textContent = 'コード'; cp.title = '機体コードをコピー';
    cp.onclick = async () => copyText(await exportCarCode(s), `「${s.name}」の機体コードをコピーしました！`);
    const dl = document.createElement('button'); dl.textContent = '削除'; let armed = 0;
    dl.onclick = () => { if (!armed) { armed = 1; dl.textContent = '本当に？'; setTimeout(() => { armed = 0; dl.textContent = '削除'; }, 2500); return; } const a = readCars().slice(); a.splice(i, 1); writeCars(a); renderSlots(); toast('「' + s.name + '」を削除しました'); };
    bt.appendChild(ld); bt.appendChild(cp); bt.appendChild(dl);
    const info = document.createElement('div'); info.className = 'inf'; info.appendChild(nm); info.appendChild(bt);
    d.appendChild(info); box.appendChild(d);
  });
}
$('bSaveCar').onclick = saveCar;
$('carName').addEventListener('keydown', e => { e.stopPropagation(); if (e.key === 'Enter') saveCar(); });
if ($('bCopyCurCode')) $('bCopyCurCode').onclick = async () => copyText(await exportCarCode(currentCarRec()), '今の機体コードをコピーしました！');
if ($('bLoadCode')) $('bLoadCode').onclick = async () => {
  const parsed = await importCarCode($('importCodeInp').value);
  if (!parsed) { toast('機体コードが正しくありません（VX6-... の文字列を貼ってください）'); return; }
  pushUndo(); S.g = parsed.gArr; S.c = parsed.cArr; S.s = parsed.sArr; S.presetId = null;
  $('carName').value = parsed.name; $('importCodeInp').value = '';
  changed(); toast(`機体コードから「${parsed.name}」を読み込みました！`);
};
if ($('bSaveCode')) $('bSaveCode').onclick = async () => {
  const parsed = await importCarCode($('importCodeInp').value);
  if (!parsed) { toast('機体コードが正しくありません（VX6-... の文字列を貼ってください）'); return; }
  const a = readCars().slice(), rec = { name: parsed.name, mass: parsed.mass, g: parsed.g, c: parsed.c, s: parsed.s };
  const idx_ = a.findIndex(x => x.name === rec.name);
  if (idx_ >= 0) a[idx_] = rec; else a.unshift(rec);
  writeCars(a); renderSlots(); populateCpuSelect(); $('importCodeInp').value = '';
  toast(`「${rec.name}」をマイガレージに追加しました！`);
};
if ($('importCodeInp')) $('importCodeInp').addEventListener('keydown', e => e.stopPropagation());

let lastTs = 0;
function loopEd(ts) {
  requestAnimationFrame(loopEd);
  const dt = Math.min(0.05, (ts - lastTs) / 1000 || 0); lastTs = ts;
  if ($('garage').hidden) return;
  if (V.fp) moveFP(dt); else moveCam(dt);
  if (V.ok) {
    if (S.dirty3) rebuild3d();
    updPlane(); placeCam(); if (V.fp && !tapOn()) showAim(null); V.r.render(V.scene, V.cam);
  }
}

{
  const dds = [['ddPreB', 'ddPre'], ['ddSlotB', 'ddSlot']];
  const closeAll = () => dds.forEach(([b, p]) => { $(p).hidden = true; $(b).setAttribute('aria-expanded', 'false'); });
  dds.forEach(([b, p]) => $(b).onclick = e => { e.stopPropagation(); const open = $(p).hidden; closeAll(); $(p).hidden = !open; $(b).setAttribute('aria-expanded', String(open)); });
  document.addEventListener('click', e => { if (!e.target.closest('.dd')) closeAll(); });
  document.addEventListener('keydown', e => { if (e.key === 'Escape') closeAll(); });
  $('presets').addEventListener('click', closeAll);
}

/* ===== 3Dレース & P2P 1対1 オンライン対戦 ===== */
const LAPS = 4, C = T.COURSE, D2R = Math.PI / 180;
const RIVALS = [
  { name: 'ブルースター', color: '#2E6FE0', id: 'wing' }
];
const LANES = [-0.095, -0.14, 0.095, 0.14];
const WHY = { tip: 'コーナーで横転', lane: 'レーンチェンジで横転', over: 'ジャンプで飛びすぎ', flipback: '空中で後ろ宙返り',
  flipfront: '空中で前のめり転倒', lift: '浮き上がってコースアウト', wave: '波状路で跳ねすぎ', stall: '失速して停止',
  blown: '向かい風にあおられてコースアウト', barricade: 'バリケードに激突して横転', short: '磁場で回路がショートして故障' };
const R = { cars: [], phase: 'idle', t: -3, speed: 1, last: 0, mode: 'over', az: 0, el: 0.36, dist: 0.36, ok: false, shown: false, endAt: 0, themeDirty: false,
  camPos: null, camLook: null, hs: 0, ptrs: new Map(), down: null,
  itemKind: '', used: false, targeting: false, events: [], fxs: [], hoverS: null, cpuPlan: null,
  raceMode: 'cpu', cpuTarget: 'pre:wing', p2pRule: 'on' };
const fmt = x => x.toFixed(2);

/* ---- P2P ネットワーク管理 (Trystero 分散リレー方式) ---- */
const APP_ID = 'voxel-4wd-p2p-v1';
const NET = {
  room: null, sendAct: null, peerId: null, isHost: false, connected: false,
  oppCar: null, myReady: false, oppReady: false, waitTimer: 0
};
function showNatWarn(msg) {
  const el = $('natWarn'); if (!el) return;
  if (!msg) { el.hidden = true; el.innerHTML = ''; }
  else { el.hidden = false; el.innerHTML = msg; }
}
function setP2pStatus(txt, state) {
  $('p2pStatTxt').textContent = txt;
  const dot = $('p2pDot');
  dot.className = 'p2p-dot' + (state === 'wait' ? ' wait' : state === 'ok' ? ' ok' : '');
  const active = !!(NET.room || NET.connected);
  $('bP2pLeave').hidden = !active;
  document.querySelectorAll('#p2pItemRule button').forEach(b => { b.disabled = active; });
}
function disconnectP2P(silent) {
  clearTimeout(NET.waitTimer);
  if (NET.room) { const r = NET.room; NET.room = null; try { r.leave(); } catch (_) {} }
  NET.sendAct = null; NET.peerId = null;
  NET.connected = false; NET.isHost = false; NET.oppCar = null; NET.myReady = false; NET.oppReady = false;
  setP2pStatus('未接続', '');
  showNatWarn('');
  if (!silent && R.raceMode !== 'cpu') setupRaceCars();
  updStartBtn();
}
function myCarPayload() {
  const nick = ($('p2pNick').value || '').trim() || 'レーサー';
  return {
    name: nick,
    g: encodeGrid(S.g),
    c: encodeGrid(S.c),
    s: encodeGrid(S.s),
    itemKind: R.itemKind,
    tieBreaker: NET.tieBreaker || (NET.tieBreaker = Math.random())
  };
}
function sendP2P(msg) {
  if (NET.sendAct && NET.connected && NET.peerId) {
    try { NET.sendAct(msg, NET.peerId); } catch (e) {}
  }
}
const P2P_TURN = [
  { urls: 'turn:openrelay.metered.ca:80', username: 'openrelayproject', credential: 'openrelayproject' },
  { urls: 'turn:openrelay.metered.ca:443', username: 'openrelayproject', credential: 'openrelayproject' },
  { urls: 'turns:openrelay.metered.ca:443?transport=tcp', username: 'openrelayproject', credential: 'openrelayproject' }
];
function connectRoom(roomName, labelTxt) {
  const strategies = (window.TrysteroStrategies && window.TrysteroStrategies.length)
    ? window.TrysteroStrategies
    : (typeof window.TrysteroJoinRoom === 'function' ? [{ name: 'default', joinRoom: window.TrysteroJoinRoom }] : []);
  if (!strategies.length) {
    toast('通信モジュールを読み込み中です。数秒後にもう一度押してください');
    return;
  }
  disconnectP2P(true);
  setP2pStatus(`${labelTxt}で待機・検索中...`, 'wait');

  // 複数方式で同じ部屋に同時参加。最初に相手と繋がった方式を採用し、残りは閉じる
  const rooms = [];
  let active = -1;
  const leaveAll = () => { rooms.forEach(r => { try { r.room.leave(); } catch (_) {} }); };
  NET.room = { leave: leaveAll };

  const adopt = (i, peerId) => {
    if (active === -1) {
      active = i;
      NET.sendAct = rooms[i].send;
      rooms.forEach((r, j) => { if (j !== i) { try { r.room.leave(); } catch (_) {} } });
    }
    return active === i;
  };

  const handleMsg = (i, data, peerId) => {
    if (!data || typeof data !== 'object') return;
    if (!adopt(i, peerId)) return;
    if (NET.peerId && NET.peerId !== peerId) return;
    if (!NET.peerId) { NET.peerId = peerId; NET.connected = true; }

    if (data.type === 'hello') {
      clearTimeout(NET.waitTimer);
      showNatWarn('');
      const firstHello = !NET.oppCar;
      NET.oppCar = data.car;
      const myT = myCarPayload().tieBreaker, opT = data.car.tieBreaker || 0;
      NET.isHost = myT !== opT ? myT > opT : String(peerId) > 'm';
      setP2pStatus(`対戦相手：${data.car.name}（接続完了・${R.p2pRule === 'off' ? 'アイテムなし' : 'アイテムあり'}）`, 'ok');
      if (firstHello) {
        SFX.match();
        toast(`${data.car.name} とマッチングしました！`);
        sendP2P({ type: 'hello', car: myCarPayload() });
      }
      setupRaceCars();
      updStartBtn();
    } else if (data.type === 'item_sel') {
      if (NET.oppCar) NET.oppCar.itemKind = data.itemKind;
    } else if (data.type === 'ready') {
      NET.oppReady = true;
      if (data.car) { NET.oppCar = data.car; setupRaceCars(); }
      toast(`${NET.oppCar ? NET.oppCar.name : '相手'} がスタート準備完了！`);
      checkBothReady();
    } else if (data.type === 'start') {
      beginOnlineRace();
    } else if (data.type === 'fire_item') {
      if (data.ev) applyOnlineEvent(data.ev, false);
    }
  };

  strategies.forEach((st, i) => {
    try {
      const room = st.joinRoom({ appId: APP_ID, turnConfig: P2P_TURN }, roomName);
      const act = room.makeAction('v4wd');
      // Trystero 0.2x系(配列API)と0.26系(オブジェクト/プロパティAPI)の両方に対応
      let send, onMsg;
      if (Array.isArray(act)) { send = act[0]; onMsg = act[1]; }
      else {
        send = (msg, target) => { const r = act.send(msg, { target }); if (r && r.catch) r.catch(() => {}); };
        onMsg = fn => { act.onMessage = (d, meta) => fn(d, meta && typeof meta === 'object' ? meta.peerId : meta); };
      }
      const setJoin = fn => { if (typeof room.onPeerJoin === 'function') room.onPeerJoin(fn); else room.onPeerJoin = fn; };
      const setLeave = fn => { if (typeof room.onPeerLeave === 'function') room.onPeerLeave(fn); else room.onPeerLeave = fn; };
      rooms[i] = { name: st.name, room, send };
      setJoin(peerId => {
        if (!adopt(i, peerId)) return;
        if (NET.connected && NET.peerId && NET.peerId !== peerId) return; // すでに1対1でマッチング済みなら無視
        clearTimeout(NET.waitTimer);
        showNatWarn('');
        NET.peerId = peerId;
        NET.connected = true; NET.myReady = false; NET.oppReady = false;
        setP2pStatus('相手を発見！データ同期中...', 'ok');
        sendP2P({ type: 'hello', car: myCarPayload() });
        // 繋がるまで定期的にhelloを再送（取りこぼし対策）
        let tries = 0;
        const retry = () => {
          if (!NET.connected || NET.oppCar || NET.peerId !== peerId) return;
          sendP2P({ type: 'hello', car: myCarPayload() });
          if (++tries < 10) NET.waitTimer = setTimeout(retry, 1500);
          else showNatWarn('相手は見つかりましたが、直接通信がネットワーク制限（NAT越え失敗）により遮断されました。スマホの4G/5G回線や別のWi-Fiに切り替えて再度お試しください。');
        };
        NET.waitTimer = setTimeout(retry, 1500);
      });
      setLeave(peerId => {
        if (active !== i) return;
        if (NET.peerId && peerId && NET.peerId === peerId) {
          const wasTrying = !NET.oppCar;
          disconnectP2P();
          if (wasTrying) showNatWarn('相手との直接通信が途中で切断されました。お互いの回線の相性（NAT制限）によって繋がらなかった可能性があります。');
          else toast('対戦相手との通信が切断されました');
        }
      });
      if (typeof onMsg === 'function') onMsg((data, peerId) => handleMsg(i, data, peerId));
    } catch (err) {
      console.error('P2P strategy error:', st.name, err);
    }
  });

  if (!rooms.some(Boolean)) {
    setP2pStatus('通信の初期化に失敗しました', '');
    disconnectP2P();
    return;
  }

  // 一定時間経っても相手が見つからない場合の案内
  NET.waitTimer = setTimeout(() => {
    if (!NET.connected && NET.room) {
      showNatWarn('相手がまだ見つかりません。相手も同じ合言葉・同じアイテム設定で検索中か確認してください。ランダム対戦は同時に検索している相手がいないとマッチしません。学校・会社などの制限回線では繋がらないことがあります。');
    }
  }, 15000);
}


function joinWordMatch() {
  const word = ($('p2pWord').value || '').trim();
  if (!word) { toast('合言葉を入力してください'); $('p2pWord').focus(); return; }
  const suffix = R.p2pRule === 'off' ? '-noitem' : '-item';
  const ruleTxt = R.p2pRule === 'off' ? 'アイテムなし' : 'アイテムあり';
  connectRoom('word-' + word + suffix, `合言葉「${word}」（${ruleTxt}）`);
}

function joinRandomMatch() {
  const suffix = R.p2pRule === 'off' ? '-noitem' : '-item';
  const ruleTxt = R.p2pRule === 'off' ? 'アイテムなし' : 'アイテムあり';
  connectRoom('random-lobby' + suffix, `ランダムマッチ（${ruleTxt}）`);
}

function populateCpuSelect() {
  const sel = $('cpuSelect'); if (!sel) return;
  const prev = sel.value || R.cpuTarget;
  sel.innerHTML = '';
  const grpPre = document.createElement('optgroup'); grpPre.label = 'サンプル機体';
  PRE.filter(p => p.id !== 'clr').forEach(p => {
    const o = document.createElement('option');
    o.value = 'pre:' + p.id;
    o.textContent = p.name + '（' + p.note + '）';
    grpPre.appendChild(o);
  });
  sel.appendChild(grpPre);
  const saved = readCars();
  if (saved.length) {
    const grpMy = document.createElement('optgroup'); grpMy.label = 'マイガレージ（自作・保存機体）';
    saved.forEach((c, idx) => {
      const o = document.createElement('option');
      o.value = 'my:' + idx;
      o.textContent = c.name + (c.mass ? `（${c.mass}g）` : '');
      grpMy.appendChild(o);
    });
    sel.appendChild(grpMy);
  }
  if (R.customCpu) {
    const grpCode = document.createElement('optgroup'); grpCode.label = '機体コードから設定中';
    const o = document.createElement('option');
    o.value = 'code:custom';
    o.textContent = `コード機体: ${R.customCpu.name}（${R.customCpu.mass}g）`;
    grpCode.appendChild(o);
    sel.appendChild(grpCode);
  }
  if ([...sel.options].some(o => o.value === prev)) sel.value = prev;
  else sel.value = 'pre:wing';
  R.cpuTarget = sel.value;
}
if ($('cpuSelect')) {
  $('cpuSelect').onchange = e => {
    R.cpuTarget = e.target.value;
    if (R.raceMode === 'cpu') setupRaceCars();
  };
}
if ($('bCpuCodeApply')) {
  $('bCpuCodeApply').onclick = async () => {
    const parsed = await importCarCode($('cpuCodeInp').value);
    if (!parsed) { toast('機体コードが正しくありません（VX6-... の文字列を貼ってください）'); return; }
    R.customCpu = parsed;
    R.cpuTarget = 'code:custom';
    populateCpuSelect();
    $('cpuSelect').value = 'code:custom';
    $('cpuCodeInp').value = '';
    if (R.raceMode === 'cpu') setupRaceCars();
    toast(`「${parsed.name}（${parsed.mass}g）」を対戦相手に設定しました！`);
  };
}
if ($('cpuCodeInp')) $('cpuCodeInp').addEventListener('keydown', e => { e.stopPropagation(); if (e.key === 'Enter') $('bCpuCodeApply').click(); });

$('modeSeg').addEventListener('click', e => {
  const b = e.target.closest('button'); if (!b) return;
  const m = b.dataset.m;
  if (R.raceMode === m) return;
  R.raceMode = m;
  document.querySelectorAll('#modeSeg button').forEach(x => x.setAttribute('aria-pressed', String(x === b)));
  disconnectP2P(true);
  $('cpuBox').hidden = m !== 'cpu';
  $('p2pBox').hidden = m === 'cpu';
  $('p2pWordRow').hidden = m !== 'word';
  $('p2pRandRow').hidden = m !== 'rand';
  R.speed = 1;
  setupRaceCars();
  updStartBtn();
  updItemUi();
});
if ($('p2pItemRule')) {
  $('p2pItemRule').addEventListener('click', e => {
    const b = e.target.closest('button'); if (!b || b.disabled) return;
    const rule = b.dataset.rule;
    if (R.p2pRule === rule) return;
    if (NET.connected || NET.room) {
      disconnectP2P();
      toast('対戦ルールを変更したため切断しました');
    }
    R.p2pRule = rule;
    document.querySelectorAll('#p2pItemRule button').forEach(x => x.setAttribute('aria-pressed', String(x === b)));
    if (R.p2pRule === 'off') {
      R.itemKind = '';
      if (NET.connected) sendP2P({ type: 'item_sel', itemKind: '' });
    }
    updItemUi();
  });
}
$('bP2pJoin').onclick = joinWordMatch;
$('bP2pRand').onclick = joinRandomMatch;
$('bP2pLeave').onclick = () => disconnectP2P();

function updStartBtn() {
  updStartBtnMain();
  const f = $('bStartFloat'), m = $('bStart');
  if (f && m) {
    const sheetOpen = $('race').classList.contains('sheet-open');
    f.hidden = sheetOpen || R.phase === 'run' || !$('results').hidden;
    f.textContent = m.textContent; f.classList.toggle('wait', m.classList.contains('wait'));
  }
}
function updStartBtnMain() {
  const b = $('bStart');
  if (R.raceMode === 'cpu') {
    b.disabled = false;
    b.classList.remove('wait');
    b.textContent = R.phase === 'run' || R.phase === 'done' ? 'もう一度レース開始！' : 'レース開始！';
  } else {
    if (!NET.connected || !NET.oppCar) {
      b.disabled = false;
      b.classList.add('wait');
      b.textContent = '相手を待機中...（接続で開始）';
    } else if (NET.myReady && !NET.oppReady) {
      b.disabled = false;
      b.classList.add('wait');
      b.textContent = '相手のスタートを待機中...';
    } else {
      b.disabled = false;
      b.classList.remove('wait');
      b.textContent = R.phase === 'run' ? '再戦を申し込む' : NET.oppReady ? 'レース開始！（相手は準備OK）' : 'レース開始！（準備OK）';
    }
  }
}

function checkBothReady() {
  updStartBtn();
  if (NET.isHost && NET.myReady && NET.oppReady) {
    sendP2P({ type: 'start' });
    beginOnlineRace();
  }
}
function beginOnlineRace() {
  NET.myReady = false; NET.oppReady = false;
  resetItem();
  R.phase = 'run'; R.t = -3; R.shown = false; R.last = 0; R.done = false;
  $('results').hidden = true;
  setRaceSheet(false); updItemUi();
  toast('1対1 オンラインレース スタート！');
}

/* ---- スマホ：レース設定シート ---- */
function setRaceSheet(open) {
  const el = $('race'); el.classList.toggle('sheet-open', !!open);
  const b = $('bRaceSheet'); if (b) b.setAttribute('aria-expanded', String(!!open));
  updStartBtn();
}
if ($('bRaceSheet')) $('bRaceSheet').onclick = () => { SFX.click(); setRaceSheet(!$('race').classList.contains('sheet-open')); };
if ($('bRaceSheetClose')) $('bRaceSheetClose').onclick = () => { SFX.click(); setRaceSheet(false); };
if ($('bRaceBack')) $('bRaceBack').onclick = () => showTab('g');
if ($('bStartFloat')) $('bStartFloat').onclick = () => startRace();

/* ---- シーン ---- */
const rc = $('rc');
function init3dRace() {
  if (!HAS3) return failRace('3D表示ライブラリを読み込めませんでした。');
  try { R.r = new THREE.WebGLRenderer({ canvas: rc, antialias: true }); } catch (e) { return failRace('このブラウザでは3D表示(WebGL)が使えません。'); }
  R.r.setPixelRatio(Math.min(window.devicePixelRatio || 1, 2));
  R.scene = new THREE.Scene(); R.cam = new THREE.PerspectiveCamera(55, 16 / 10, 0.01, 60);
  R.scene.add(new THREE.HemisphereLight(0xffffff, 0x778899, 0.75));
  const dl = new THREE.DirectionalLight(0xffffff, 0.7); dl.position.set(3, 8, 4); R.scene.add(dl);
  R.camPos = new THREE.Vector3(0, 1, 1); R.camLook = new THREE.Vector3();
  R.ok = true; rebuildWorld();
}
function failRace(msg) { const d = document.createElement('div'); d.className = 'nowebgl'; d.textContent = msg; rc.parentElement.appendChild(d); }
function layoutRace() {
  layoutMini();
  if (!R.ok) return; const w = rc.parentElement.clientWidth || 640, h = rc.parentElement.clientHeight || 400;
  R.r.setSize(w, h, false); R.cam.aspect = w / h; R.cam.updateProjectionMatrix();
}
function rebuildWorld() {
  if (!R.ok) return;
  if (R.world) { R.scene.remove(R.world); disposeGroup(R.world); }
  const w = new THREE.Group();
  const gm = new THREE.Mesh(new THREE.PlaneGeometry(60, 60), new THREE.MeshLambertMaterial({ color: new THREE.Color(TH.grass) }));
  gm.rotation.x = -Math.PI / 2; gm.position.set(2.2, -0.004, -1.45); w.add(gm);
  const gh = new THREE.GridHelper(60, 120, new THREE.Color(TH.line2), new THREE.Color(TH.line2)); gh.position.set(2.2, -0.002, -1.45);
  gh.material.transparent = true; gh.material.opacity = 0.35; w.add(gh);
  w.add(buildTrack());
  R.world = w; R.scene.add(w);
  R.scene.background = new THREE.Color(TH.bg); R.scene.fog = new THREE.Fog(new THREE.Color(TH.bg), 7, 26);
  R.themeDirty = false;
}
function buildTrack() {
  const hw = C.F.width / 2, ds = 0.04, n = Math.ceil(C.length / ds), NJ = 10, J = C.F.jump, W = C.F.wave;
  const pos = [], col = [];
  const base = new THREE.Color(TH.track), light = base.clone().multiplyScalar(1.07), white = new THREE.Color('#f2f4f7'),
    hazY = new THREE.Color('#f4b400'), hazK = new THREE.Color('#1b1f27'), green = new THREE.Color(TH.good), amber = new THREE.Color('#e0a020'),
    wallA = new THREE.Color(TH.accent), wallB = new THREE.Color('#f2f4f7'), dark = new THREE.Color('#2a303a'), laneC = new THREE.Color(TH.cool);
  const lipEnd = J.s0 + J.rampLen, landEnd = lipEnd + J.gap + J.landLen;
  const H = s => C.elev(s) + (s >= W.s0 && s <= W.s1 ? W.amp * 1.8 * Math.sin(2 * Math.PI * (s - W.s0) / W.lam) * Math.min(1, (s - W.s0) / 0.15, (W.s1 - s) / 0.15) : 0);
  const P = (s, lat) => { const p = C.pos(s, lat); return [p.x, H(s), -p.y]; };
  const quad = (a, b, c, d, color) => { for (const v of [a, b, c, a, c, d]) { pos.push(v[0], v[1], v[2]); col.push(color.r, color.g, color.b); } };
  const colorAt = (s, j) => {
    const mid = j === NJ / 2 - 1 || j === NJ / 2;
    if (s < 0.1 || s > C.length - 0.06) return ((Math.floor(s / 0.05) + j) % 2) ? dark : white;
    if (s >= J.s0 && s < lipEnd) return Math.floor((s - J.s0) / 0.07) % 2 ? hazK : hazY;
    if (s >= lipEnd && s < landEnd) return mid && (s % 0.12 < 0.07) ? white : green.clone().lerp(base, 0.55);
    if (s >= W.s0 && s <= W.s1 && Math.sin(2 * Math.PI * (s - W.s0) / W.lam) > 0.35) return amber;
    if (C.inLane(s) && (j === 0 || j === NJ - 1)) return laneC;
    if (mid && (s % 0.12 < 0.07)) return white;
    return ((Math.floor(s / 0.2) + j) % 2) ? light : base;
  };
  for (let i = 0; i < n; i++) {
    const s0 = i * ds, s1 = Math.min((i + 1) * ds, C.length - 1e-6), sm = (s0 + s1) / 2;
    for (let j = 0; j < NJ; j++) {
      const l0 = -hw + 2 * hw * j / NJ, l1 = -hw + 2 * hw * (j + 1) / NJ;
      quad(P(s0, l0), P(s1, l0), P(s1, l1), P(s0, l1), colorAt(sm, j));
    }
    for (const side of [-1, 1]) {
      const lw = side * hw, lo = side * (hw + 0.012), wc = Math.floor(sm / 0.18) % 2 ? wallA : wallB;
      const a = P(s0, lw), b = P(s1, lw), a2 = [a[0], a[1] + 0.035, a[2]], b2 = [b[0], b[1] + 0.035, b[2]];
      quad(a, b, b2, a2, wc);
      const ao = P(s0, lo), bo = P(s1, lo), ao2 = [ao[0], ao[1] + 0.035, ao[2]], bo2 = [bo[0], bo[1] + 0.035, bo[2]];
      quad(a2, b2, bo2, ao2, wc.clone().multiplyScalar(0.85));
      quad(ao, bo, bo2, ao2, wc.clone().multiplyScalar(0.7));
      quad([ao[0], 0, ao[2]], [bo[0], 0, bo[2]], bo, ao, dark);
    }
  }
  const geo = new THREE.BufferGeometry();
  geo.setAttribute('position', new THREE.Float32BufferAttribute(pos, 3)); geo.setAttribute('color', new THREE.Float32BufferAttribute(col, 3));
  geo.computeVertexNormals();
  return new THREE.Mesh(geo, new THREE.MeshLambertMaterial({ vertexColors: true, side: THREE.DoubleSide }));
}

function makeEntry(name, color, grid, me, lane, id, cols, shapes) {
  const an = T.analyze(grid, shapes), car = T.carParams(an);
  const sim = T.simulate(car, LAPS);
  return { name, color, grid, cols: cols || newColors(), shapes: shapes || T.newShapes(), an, car, sim, baseSim: sim, me, lat: lane, id };
}
function tintRival(r, ent) {
  for (let k = 0; k < ent.grid.length; k++) if (ent.grid[k] === 1) ent.cols[k] = 9; // #1D4ED8 (レーシングブルー)
  return ent;
}
function buildMeshes() {
  if (!R.ok) return;
  if (R.carRoot) { R.scene.remove(R.carRoot); disposeGroup(R.carRoot); }
  const root_ = new THREE.Group();
  R.cars.forEach(c => {
    const inner = buildCarGroup(c.grid, { edges: false, c: c.cols, s: c.shapes }); inner.position.set(-CX / 2, 0, -CZ / 2);
    const outer = new THREE.Group(); outer.scale.setScalar(0.005); outer.add(inner);
    const mk = new THREE.Mesh(new THREE.ConeGeometry(3.2, 7, 4), new THREE.MeshBasicMaterial({ color: new THREE.Color(c.me ? TH.accent : c.color) }));
    mk.rotation.x = Math.PI; mk.position.set(0, 20, 0); outer.add(mk);
    c.mesh = outer; c.wheels = inner.userData.wheels; c.marker = mk; root_.add(outer);
  });
  R.carRoot = root_; R.scene.add(root_);
}
function carState(car, t) {
  const sim = car.sim, rec = sim.rec, n = rec.t.length, tEnd = rec.t[n - 1];
  if (t <= 0) return { s: 0, v: 0, hop: 0, pitch: 0, tip: 0, geff: 1, air: 0, mode: 'run' };
  if (t < tEnd) {
    let lo = 0, hi = n - 1;
    while (hi - lo > 1) { const m = (lo + hi) >> 1; if (rec.t[m] <= t) lo = m; else hi = m; }
    const f = (t - rec.t[lo]) / Math.max(1e-6, rec.t[hi] - rec.t[lo]), L = k => rec[k][lo] + (rec[k][hi] - rec[k][lo]) * f;
    return { s: L('s'), v: L('v'), hop: L('hop'), pitch: L('pitch'), tip: L('tip'), geff: L('geff'), air: rec.air[lo], mode: 'run' };
  }
  if (sim.finish !== null) {
    const d = t - tEnd, vE = rec.v[n - 1];
    return { s: sim.total + vE * 0.9 * (1 - Math.exp(-d / 0.9)), v: vE * Math.exp(-d / 0.9), hop: 0, pitch: 0, tip: 0, geff: 1, air: 0, mode: 'fin' };
  }
  return { s: rec.s[n - 1], v: 0, v0: rec.v[n - 1], hop: 0, pitch: 0, tip: rec.tip[n - 1], geff: 1, air: 0, mode: 'crash', tc: t - tEnd };
}
const endTime = car => car.sim.rec.t[car.sim.rec.t.length - 1] + (car.sim.dnf ? 1.8 : 0);
const smooth = x => x * x * (3 - 2 * x);
function placeCar(car, st, idx) {
  const L = C.length, sl = ((st.s % L) + L) % L;
  let s = st.s, lat = car.lat, y = 0, roll = 0, pitch = 0, yawAdd = 0;
  const ks = C.kappa(sl);
  if (st.mode === 'crash') {
    const tc = st.tc, why = car.sim.dnf.reason;
    const out = why === 'blown' ? ((car.sim.dnf.info && car.sim.dnf.info.dir) || 1) : ks > 0.05 ? -1 : ks < -0.05 ? 1 : (idx % 2 ? 1 : -1);
    s += (st.v0 || 0) * 0.9 * (1 - Math.exp(-tc / 0.45));
    const k = Math.min(tc / 0.9, 1);
    if (why === 'stall' || why === 'short') { y = C.elev(s); }
    else {
      lat += out * Math.min(tc * 0.5, 0.3) * (why === 'blown' ? 2.4 : why === 'lift' || why === 'over' ? 1.4 : 1);
      const air = Math.sin(k * Math.PI) * (why === 'lift' ? 0.34 : why === 'blown' ? 0.26 : why === 'over' ? 0.22 : 0.12);
      y = C.elev(s) * (1 - smooth(k)) + air;
      if (why === 'flipback') pitch = Math.min(tc * 6, Math.PI * 1.1);
      else if (why === 'barricade') pitch = -Math.min(tc * 7, Math.PI * 1.1);
      else if (why === 'blown') { pitch = Math.min(tc * 3.5, 1.3); roll = out * Math.min(tc * 4, Math.PI * 1.5); }
      else if (why === 'flipfront') pitch = -Math.min(tc * 6, Math.PI * 1.1);
      else if (why === 'lift') { pitch = -Math.min(tc * 2.5, 1.4); roll = out * Math.min(tc * 3, Math.PI); }
      else roll = -out * Math.min(tc * 4.5, Math.PI * 0.62);
      yawAdd = out * Math.min(tc * 1.2, 0.5);
    }
  } else {
    y = C.elev(s) + (st.air ? st.hop : st.hop * 0.9);
    pitch = (st.air ? st.pitch * D2R : C.phi(sl) + st.pitch * D2R * 0.4);
    roll = (ks >= 0 ? 1 : -1) * clamp(st.tip, 0, 1.2) * 0.2;
  }
  const p = C.pos(s, lat);
  car.mesh.position.set(p.x, y, -p.y);
  car.mesh.rotation.set(roll, p.h + yawAdd, pitch, 'YZX');
  const ang = -s * 18; for (const w of car.wheels) w.rotation.z = ang;
  return { p, y };
}

/* ---- カメラ ---- */
function updCamera(dt, snapNow) {
  const me = R.cars[0]; if (!me) return;
  const m = me.mesh.position, h = me.mesh.rotation.y;
  let pos, look;
  if (R.mode === 'chase') {
    const st = me.st;
    const curS = st ? st.s : 0;
    const tp = C.pos(curS, me.lat);
    const targetH = tp.hd != null ? tp.hd : h;

    // 角度差を [-π, π] に正規化（周回を重ねても360度逆回転しない）
    const diffH = Math.atan2(Math.sin(targetH - R.hs), Math.cos(targetH - R.hs));
    R.hs = snapNow ? targetH : R.hs + diffH * (1 - Math.exp(-dt * 9));

    // 車高の上下動（波状路の激しい小刻み振動）を吸収し、滑らかな高さを追従
    const baseElev = C.elev(curS);
    const jumpY = (st && st.air) ? st.hop * 0.7 : 0;
    const targetY = (st && st.mode === 'crash') ? m.y + 0.04 : (baseElev + jumpY + 0.03);
    if (snapNow || R.camY == null) R.camY = targetY;
    else R.camY += (targetY - R.camY) * (1 - Math.exp(-dt * 12));

    const hd = R.hs;
    const distH = R.dist * Math.cos(R.el);
    const distV = R.dist * Math.sin(R.el);
    const ph = -hd + Math.PI + R.az;

    // カメラ位置：マシンの水平位置から smoothed heading の真後ろへ
    pos = new THREE.Vector3(
      m.x + Math.cos(ph) * distH,
      R.camY + distV,
      m.z + Math.sin(ph) * distH
    );
    // 注視点：マシン本体の少し前方を滑らかに見据える（カーブでもマシンが画面中央から外れない）
    look = new THREE.Vector3(
      m.x + Math.cos(hd) * 0.08,
      R.camY + 0.015,
      m.z - Math.sin(hd) * 0.08
    );

    // 追従モードでは遅延ブレ（ゴム紐効果）を防ぐためダイレクト反映
    if (snapNow) {
      R.camPos.copy(pos);
      R.camLook.copy(look);
    } else {
      const k = 1 - Math.exp(-dt * 25);
      R.camPos.lerp(pos, k);
      R.camLook.lerp(look, k);
    }
  } else {
    const portrait = R.cam.aspect < 0.85;
    const c = new THREE.Vector3(2.2, 0, -1.45), ph = (portrait ? 0 : Math.PI / 2) + R.az, el = (portrait ? 0.5 : 0.95) + (R.el - 0.36);
    const d = R.dist * 11 * (portrait ? clamp(1.0 / R.cam.aspect, 1.2, 2.3) : 1);
    pos = new THREE.Vector3(c.x + Math.cos(ph) * d * Math.sin(el), c.y + d * Math.cos(el), c.z + Math.sin(ph) * d * Math.sin(el)); look = c;
    const k = snapNow ? 1 : Math.min(1, dt * 4);
    R.camPos.lerp(pos, k); R.camLook.lerp(look, k);
  }
  R.cam.position.copy(R.camPos); R.cam.lookAt(R.camLook);
  if (R.cam.fov !== 55) { R.cam.fov = 55; R.cam.updateProjectionMatrix(); }
}
document.querySelectorAll('#camb button[data-c]').forEach(b => b.onclick = () => {
  R.mode = b.dataset.c; R.az = 0; R.el = 0.36; R.dist = 0.36; R.snap = true;
  document.querySelectorAll('#camb button[data-c]').forEach(x => x.setAttribute('aria-pressed', String(x === b)));
});
rc.addEventListener('pointerdown', e => {
  try { rc.setPointerCapture(e.pointerId); } catch (_) {}
  R.ptrs.set(e.pointerId, { x: e.clientX, y: e.clientY });
  R.tdown = { x: e.clientX, y: e.clientY };
  if (R.ptrs.size === 2) {
    const [a, b] = [...R.ptrs.values()];
    R.pinch0 = Math.hypot(a.x - b.x, a.y - b.y);
    R.dist0 = R.dist;
    R.tdown = null;
  }
});
rc.addEventListener('pointermove', e => {
  if (R.targeting) R.hoverS = screenNearest(e);
  const p = R.ptrs.get(e.pointerId); if (!p) return;
  if (R.ptrs.size === 2 && R.pinch0) {
    p.x = e.clientX; p.y = e.clientY;
    const [a, b] = [...R.ptrs.values()];
    const d = Math.hypot(a.x - b.x, a.y - b.y);
    if (d > 10) R.dist = clamp(R.dist0 * (R.pinch0 / d), 0.2, 1.6);
    return;
  }
  const dx = e.clientX - p.x, dy = e.clientY - p.y;
  p.x = e.clientX; p.y = e.clientY;
  if (R.ptrs.size === 1) {
    R.az -= dx * 0.008;
    R.el = clamp(R.el + dy * 0.006, 0.05, 1.3);
  }
});
const upR = e => {
  R.ptrs.delete(e.pointerId);
  if (R.ptrs.size < 2) R.pinch0 = null;
};
rc.addEventListener('pointerup', e => {
  const d = R.tdown;
  upR(e);
  R.tdown = null;
  if (R.targeting && d && Math.hypot(e.clientX - d.x, e.clientY - d.y) < 9) {
    const sc = screenNearest(e);
    if (sc !== null) fireItem(sc);
    else toast('コースの上をタップしてね');
  }
});
rc.addEventListener('pointercancel', e => { upR(e); R.tdown = null; });
rc.addEventListener('wheel', e => { e.preventDefault(); R.dist = clamp(R.dist * Math.exp(e.deltaY * 0.001), 0.2, 1.6); }, { passive: false });

function zoneLabel(st) {
  const F = C.F, sl = ((st.s % C.length) + C.length) % C.length, j = F.jump;
  if (st.air) return 'ジャンプ中！';
  if (sl >= j.s0 && sl < j.s0 + j.rampLen) return '立体レーンチェンジ：山';
  if (sl >= j.s0 + j.rampLen && sl < j.s0 + j.rampLen + j.landLen + j.gap) return '着地ゾーン';
  if (sl >= F.wave.s0 && sl <= F.wave.s1) return 'ウェーブ';
  if (C.inLane(sl)) return 'レーンチェンジ';
  const k = Math.abs(C.kappa(sl)); if (k > 0.3) return 'コーナー R' + (1 / k).toFixed(1);
  return 'ストレート';
}
function updLive(car, st) {
  $('lvV').textContent = (st.v * 3.6).toFixed(1) + ' km/h'; $('lvVb').style.width = clamp(st.v / 6, 0, 1) * 100 + '%';
  const tp = clamp(st.tip, 0, 1.2); $('lvT').textContent = Math.round(tp * 100) + '%'; $('lvTb').style.width = clamp(tp, 0, 1) * 100 + '%';
  $('lvTb').style.background = tp > 0.85 ? 'var(--bad)' : tp > 0.6 ? 'var(--warn)' : 'var(--good)';
  $('lvG').textContent = st.geff.toFixed(2) + 'G'; $('lvGb').style.width = clamp(st.geff / 1.8, 0, 1) * 100 + '%';
  $('lvGb').style.background = st.geff < 0.75 ? 'var(--bad)' : 'var(--ink)';
}
function buildBoard() {}
function updBoard() {}

function finalRanking() {
  return R.cars.slice().sort((a, b) => {
    const fa = a.sim.finish, fb = b.sim.finish;
    if (fa !== null && fb !== null) return fa - fb; if (fa !== null) return -1; if (fb !== null) return 1; return b.sim.dnf.s - a.sim.dnf.s;
  });
}
function adviceHTML(me, rank) {
  const sim = me.sim, an = me.an, st = sim.stats, d = sim.dnf, W = C.F.wave, J = C.F.jump, items = [];
  let head;
  if (d) {
    const i = d.info || {};
    head = WHY[d.reason] + 'でリタイア（' + (d.s / C.length).toFixed(1) + '周目付近）';
    switch (d.reason) {
      case 'tip': case 'lane':
        items.push(`横転ゲージが ${Math.round((i.tip || 1) * 100)}% に達しました（100%で横転）。速度 ${(i.v * 3.6).toFixed(1)}km/h、半径${(1 / Math.max(i.kap, 0.01)).toFixed(1)}mの曲がりです。`);
        items.push(`重心の高さは ${(an.cgy * 5).toFixed(1)}mm、左右のずれは ${((an.cgz - T.ZC) * 5).toFixed(1)}mm。おもりを下の段・中央に置く、上のブロックを削る、リアウイングで下向きの力を足す、のどれかが効きます。`); break;
      case 'over':
        items.push(`立体レーンチェンジの山で約 ${i.d.toFixed(2)}m 飛び、着地ゾーン（${J.landLen}m）を越えました。実効重力は ${i.geff.toFixed(2)}G です。`);
        items.push('後ろ上がりのウイングで押さえつけるか、山に入る速度を落とすと収まります。'); break;
      case 'flipback':
        items.push(`着地時の機首角が +${i.theta.toFixed(0)}°（±26°で転倒）。空中で機首が上がり、後ろに宙返りしました。`);
        items.push('リアウイングの下向きの力や背の高い後部が機首を上げています。おもりを前寄りに置くか、リアウイングを小さく。'); break;
      case 'flipfront':
        items.push(`着地時の機首角が ${i.theta.toFixed(0)}°（−26°で転倒）。前のめりに転びました。`);
        items.push('前側に下向きの力が集まっているか、重心が前寄りです。おもりを後ろへ。'); break;
      case 'lift':
        items.push(`接地の強さが ${i.geff.toFixed(2)}G まで落ち、浮き上がりました。車重は ${an.mass.toFixed(0)}g です。`);
        items.push('軽い車ほど同じ浮く力の影響を受けます。広い天井や前上がりの板を減らし、後ろ上がりのウイングを足すか、おもりで重くしましょう。'); break;
      case 'wave':
        items.push(`波状路での跳ね高さが ${(i.hb * 1000).toFixed(0)}mm（限界 ${(W.limit * 1000).toFixed(0)}mm）。速度 ${(i.v * 3.6).toFixed(1)}km/h で突っ込んでいます。`);
        items.push('下向きの力を足して接地を強くするか、空気抵抗を増やして速度を抑えましょう。'); break;
      case 'blown':
        items.push(`おじゃまの強力ファンの強い向かい風で機体が煽られ、コースアウトしました（車重 ${an.mass.toFixed(0)}g・接地 ${(i.geff || 0).toFixed(2)}G）。`);
        items.push('極端に軽いマシンや接地が弱いマシンは、向かい風で稀に吹き飛ばされます。鉄ブロックで重くするか、ウイングで接地を強めましょう。'); break;
      case 'short':
        items.push(`おじゃまの磁石の強力な磁場を受け、鉄ブロック（${(i.ironMass || an.mHeavy || 0).toFixed(0)}g）に誘導電流が流れて回路がショート・故障しました。`);
        items.push('鉄ブロックを大量に積んだ磁石に極端に弱いマシンは、磁場で稀に一発リタイアします。鉄を減らして普通のブロックや空力（ウイング）を活用しましょう。'); break;
      case 'barricade':
        items.push(`おじゃまのバリケードに ${(i.v * 3.6).toFixed(1)}km/h で正面衝突して横転しました。先端の尖りは ${Math.round((i.nose || 0) * 100)}% です。`);
        items.push('先端が極端に平らだと、稀に衝撃で一発横転します。くさびや四角錐で先端を細く尖らせると、障害物を左右に受け流せます。'); break;
      case 'stall':
        items.push('空気抵抗や車重が大きすぎて、モーターの力では進めなくなりました。');
        items.push(`空気抵抗は ${an.D.toFixed(1)}、車重は ${an.mass.toFixed(0)}g。前面の壁を斜めにする、余分なブロックを削る、で走れます。`); break;
    }
  } else {
    head = rank === 1 ? '優勝！ いい走りです' : rank + '位でゴール';
    const others = R.cars.filter(c => !c.me);
    const best = others.length ? Math.max(...others.map(c => c.sim.stats.topV)) : st.topV;
    items.push(`最高速は ${(st.topV * 3.6).toFixed(1)}km/h（相手最速 ${(best * 3.6).toFixed(1)}km/h）。`);
    if (an.D > 14) items.push('空気抵抗が大きめです。前面の壁を斜めに、上から見た先端も細くすると伸びます。');
    else if (an.mass > 115) items.push(`車重 ${an.mass.toFixed(0)}g。軽くするほど加速は良くなります（ただし軽すぎると浮きます）。`);
    if (st.minG < 0.8) items.push(`接地の強さが最低 ${st.minG.toFixed(2)}G まで下がりました。0.68Gを割ると浮いてコースアウトです。`);
    if (st.maxTip > 0.85) items.push(`横転ゲージが最大 ${Math.round(st.maxTip * 100)}% でギリギリでした。重心をもう少し下げると安心です。`);
    if (st.waveHop > W.limit * 0.85) items.push(`波状路の跳ね高さが ${(st.waveHop * 1000).toFixed(0)}mm（限界 ${(W.limit * 1000).toFixed(0)}mm）。`);
    if (st.jump && Math.abs(st.jump.theta) > 18) items.push(`山の着地姿勢が ${st.jump.theta.toFixed(0)}°（±26°で転倒）。前後の重量バランスを見直そう。`);
    if (items.length < 2) items.push('さらに詰めるなら、ウイングの角度やおもりの位置を少しずつ変えて、風洞データの変化を見ながら試してみてください。');
  }
  return `<b>${head}</b><ul>${items.map(x => '<li>' + x + '</li>').join('')}</ul>`;
}
function showResults() {
  R.shown = true;
  const rank = finalRanking(), me = R.cars.find(c => c.me), myRank = rank.indexOf(me) + 1, w = rank[0].sim.finish;
  const win = myRank === 1 && me.sim.finish !== null;
  SFX.finish(win);
  $('resTitle').textContent = win ? '結果：勝利！' : '結果';
  $('resTable').innerHTML = rank.map((c, i) => {
    const t = c.sim.finish;
    const cell = t !== null ? fmt(t) + '秒' + (i && w !== null ? `<br><span class="small">+${fmt(t - w)}</span>` : '') : `<span style="color:var(--bad)">× ${WHY[c.sim.dnf.reason]}</span>`;
    return `<tr class="${c.me ? 'me' : ''}"><td>${i + 1}</td><td><b>${c.name}</b><br><span class="small">${c.an.mass.toFixed(0)}g</span></td><td class="t">${cell}</td></tr>`;
  }).join('');
  $('advice').innerHTML = adviceHTML(me, myRank) + itemReportHTML(); $('results').hidden = false;
  updStartBtn();
}
if ($('resClose')) $('resClose').onclick = () => { $('results').hidden = true; updStartBtn(); };
if ($('bResRestart')) $('bResRestart').onclick = () => { $('results').hidden = true; startRace(); };
if ($('bResGarage')) $('bResGarage').onclick = () => { $('results').hidden = true; showTab('g'); };
if ($('results')) {
  $('results').onclick = e => {
    if (e.target === $('results')) { $('results').hidden = true; updStartBtn(); }
  };
}

/* ---- 進行 ---- */
function setReady() {
  resetItem(); R.phase = 'ready'; R.t = -3; R.shown = false; R.last = 0; R.snap = true; R.hs = 0; R.camY = null;
  $('results').hidden = true; $('cd').textContent = '';
  updStartBtn();
}
function makeCpuEntry() {
  const target = R.cpuTarget || 'pre:wing';
  if (target === 'code:custom' && R.customCpu) {
    const c = R.customCpu;
    return makeEntry('コード: ' + c.name, '#2E6FE0', c.gArr.slice(), false, LANES[2], 'code_custom', c.cArr.slice(), c.sArr.slice());
  }
  if (target.startsWith('my:')) {
    const idx = parseInt(target.slice(3), 10);
    const saved = readCars()[idx];
    if (saved) {
      const g = decodeGrid(saved.g), c = decodeColors(saved.c, g), s = decodeShapes(saved.s, g);
      return makeEntry('CPU: ' + saved.name, '#2E6FE0', g, false, LANES[2], 'my_' + idx, c, s);
    }
  }
  const pid = target.startsWith('pre:') ? target.slice(4) : 'wing';
  const p = PRE.find(x => x.id === pid) || PRE.find(x => x.id === 'wing');
  const g = p.fn(), s = p.sfn ? p.sfn() : T.newShapes();
  return tintRival({ color: '#2E6FE0' }, makeEntry('CPU: ' + p.name, '#2E6FE0', g, false, LANES[2], p.id, newColors(), s));
}
function setupRaceCars() {
  const myName = R.raceMode === 'cpu' ? 'あなた' : (($('p2pNick').value || '').trim() || 'あなた');
  const cars = [makeEntry(myName, TH.accent, S.g.slice(), true, LANES[0], null, S.c.slice(), S.s.slice())];
  if (R.raceMode === 'cpu') {
    cars.push(makeCpuEntry());
  } else if (NET.connected && NET.oppCar) {
    const oc = NET.oppCar;
    const og = decodeGrid(oc.g);
    const ocol = decodeColors(oc.c, og);
    const osh = decodeShapes(oc.s, og);
    cars.push(makeEntry(oc.name || 'ライバル', '#2E6FE0', og, false, LANES[2], 'opp', ocol, osh));
  }
  killFx();
  R.cars = cars; R.endAt = Math.max(...cars.map(endTime));
  buildBoard(); layoutRace(); buildMeshes(); setReady(); R.hs = C.pos(0, 0).h;
  R.used = false; R.targeting = false; R.events = []; renderRates(); updItemUi();
}
function enterRace() {
  populateCpuSelect();
  setupRaceCars();
}
function startRace() {
  if (R.raceMode === 'cpu') {
    resetItem(); R.phase = 'run'; R.t = -3; R.shown = false; R.last = 0; R.done = false;
    if (R.itemKind) {
      const kinds = ['fan', 'mag', 'bar'];
      const kind = kinds[Math.floor(Math.random() * kinds.length)];
      const maxT = Math.max(2.5, Math.min(R.endAt * 0.65, 7.0));
      R.cpuPlan = { kind, fireAt: 1.0 + Math.random() * (maxT - 1.0), fired: false };
    }
    $('results').hidden = true; setRaceSheet(false); updItemUi();
  } else {
    if (!NET.connected || !NET.oppCar) {
      setRaceSheet(true);
      toast('対戦相手とマッチングするまでお待ちください（合言葉を入れて接続、またはランダム対戦）');
      return;
    }
    NET.myReady = true;
    sendP2P({ type: 'ready', car: myCarPayload() });
    checkBothReady();
  }
}
$('bStart').onclick = startRace;

function loopRace(ts) {
  requestAnimationFrame(loopRace);
  if ($('race').hidden || !R.cars.length) { R.last = 0; SFX.stopMotor(); return; }
  const dt = R.last ? Math.min(0.05, (ts - R.last) / 1000) : 0.016; R.last = ts;
  if (R.phase === 'run') R.t += dt * R.speed;
  const t = R.phase === 'ready' ? 0 : R.t;
  if (R.themeDirty) { rebuildWorld(); buildMeshes(); }
  R.cars.forEach((c, i) => {
    const prevMode = c.st ? c.st.mode : 'run';
    const st = carState(c, t); c.st = st;
    if (R.phase === 'run' && prevMode !== 'crash' && st.mode === 'crash' && !c.crashedSfx) { c.crashedSfx = true; SFX.crash(); }
    if (R.ok) placeCar(c, st, i);
  });
  const me = R.cars[0], mst = me.st;
  if (R.phase === 'run' && t >= 0) {
    if (!R.prevAir && mst.air) SFX.jump();
    else if (R.prevAir && !mst.air && mst.mode === 'run') SFX.land();
    R.prevAir = !!mst.air;
  }
  SFX.motor(mst.v, mst.air, R.phase === 'run' && t >= 0 && mst.mode === 'run');
  if (R.phase === 'run' && R.raceMode === 'cpu' && R.cpuPlan && !R.cpuPlan.fired && t >= R.cpuPlan.fireAt && !R.shown) {
    R.cpuPlan.fired = true;
    const cKind = R.cpuPlan.kind, cSpec = ITEMS[cKind], t0 = Math.max(0, t);
    const targetS = ((mst.s + 0.7 + Math.random() * 1.1) % C.length + C.length) % C.length;
    applyOnlineEvent({ kind: cKind, id: R.events.length + 1, t0, t1: t0 + 1.0, sc: targetS, r: cSpec.r, dir: 1, seed: Math.random() }, false);
  }
  if (R.ok) { updCamera(dt, R.snap); R.snap = false; R.cars.forEach(c => { c.marker.rotation.y += dt * 2; c.marker.position.y = 20 + Math.sin(ts / 300) * 1.2; }); R.r.render(R.scene, R.cam); }
  updLive(me, mst); updBoard(t); updFx(t, ts); updAimFx(); drawMini(t);
  const lap = clamp(Math.floor(mst.s / C.length) + 1, 1, LAPS);
  if ($('miniLapTxt')) $('miniLapTxt').textContent = mst.mode === 'fin' ? `ゴール！（${LAPS}/${LAPS}周）` : `${lap} / ${LAPS} 周目`;
  { const arm = R.phase === 'run' && !R.used && R.t >= 0 && !!R.itemKind && !R.done; if (arm !== R.targeting) { R.targeting = arm; if (!arm) R.hoverS = null; updItemUi(); } }
  const cd = $('cd'), cdTxt = R.phase === 'ready' ? '' : t < 0 ? String(Math.ceil(-t)) : t < 0.8 ? 'GO!' : '';
  if (cd.textContent !== cdTxt) { cd.textContent = cdTxt; if (cdTxt) SFX.count(cdTxt); }
  if (R.phase === 'run' && !R.shown) {
    const myEnd = endTime(me) + (me.sim.dnf ? 0 : 1.2);
    if (t >= Math.min(R.endAt, myEnd + 3)) { R.phase = 'done'; R.targeting = false; showResults(); updItemUi(); }
  }
}

/* ---- おじゃまアイテム ---- */
const ITEMS = {
  fan: { name: '強力ファン', r: 0.9, col: '#3aa7ff', text: '指定した場所に<b>1秒間、正面から強い向かい風</b>を吹かせます。<br><span class="bad">弱い形</span>：軽いマシン（足止め・極端に軽いと稀にコースアウト）　<span class="good">強い形</span>：重いマシン・流線型' },
  mag: { name: '磁石', r: 0.9, col: '#8b5cf6', text: '指定した場所に<b>1秒間、強力な磁場</b>を作ります。<br><span class="bad">弱い形</span>：重いマシン（足止め・鉄が大量だと稀に回路ショート）　<span class="good">強い形</span>：鉄を使わない軽いマシン' },
  bar: { name: 'バリケード', r: 0.12, col: '#ef4444', text: 'コース上の指定した場所に<b>1秒間、障害物</b>を出します。<br><span class="bad">弱い形</span>：先端が平らなマシン（大幅減速・極端に平らだと稀に横転）　<span class="good">強い形</span>：先端がくさび型に尖ったマシン' }
};
function renderRates() {}
function updItemUi() {
  const isNoItemMatch = R.raceMode !== 'cpu' && R.p2pRule === 'off';
  if (isNoItemMatch) R.itemKind = '';
  const run = R.phase === 'run';
  document.querySelectorAll('#itemSeg button').forEach(b => {
    b.setAttribute('aria-pressed', String(b.dataset.k === R.itemKind));
    b.disabled = run || isNoItemMatch;
  });
  if (isNoItemMatch) {
    $('itemInfo').innerHTML = '<b>【アイテムなしルール】</b><br><span class="small" style="color:var(--ink2)">対戦モードで「アイテムなし」が設定されているため、アイテムは選択・使用できません。純粋なマシン性能と走りで競い合います！</span>';
  } else {
    const actText = isMobileScreen() ? 'タップ' : 'クリック';
    $('itemInfo').innerHTML = R.itemKind ? ITEMS[R.itemKind].text + `<br><span class="small">効くのは<b>指定した場所だけ</b>（コース全体ではありません）。そこを通る全車に効くので自分も注意！レース中に<b>コースの好きな場所を${actText}</b>（3D画面でも全体図でもOK）するとその場所で発動します。1回だけなので、タイミングと場所を考えて！</span>` : `使わない場合は「なし」。アイテムを選んでおくと、レース中にコース上の好きな場所を${actText}して1回だけ発動できます。`;
  }
  $('bItem').hidden = true;
  $('mini').classList.toggle('aim', R.targeting);
  const ban = $('aimBanner');
  if (ban) {
    ban.hidden = !R.targeting;
    if (R.targeting) {
      const actWord = isMobileScreen() ? 'タップ' : 'クリック';
      ban.textContent = (R.itemKind && ITEMS[R.itemKind]) ? `${ITEMS[R.itemKind].name}：コース上を${actWord}で発動！` : '';
    }
  }
  if (R.lastAim !== R.targeting) { R.lastAim = R.targeting; if (R.mctx) layoutMini(); }
}
$('itemSeg').addEventListener('click', e => {
  const isNoItemMatch = R.raceMode !== 'cpu' && R.p2pRule === 'off';
  if (isNoItemMatch) return;
  const b = e.target.closest('button'); if (!b || b.disabled) return;
  R.itemKind = b.dataset.k;
  if (NET.connected) sendP2P({ type: 'item_sel', itemKind: R.itemKind });
  updItemUi();
});

const mini = $('mini'); let MP = null;
function layoutMini() {
  mini.style.width = ''; mini.style.height = ''; const w = mini.clientWidth || 300, h = Math.round(w * 190 / 300); R.mctx = fitCanvas(mini, w, h); R.mw = w; R.mh = h;
  if (!MP) { MP = []; for (let s = 0; s < C.length; s += 0.08) { const p = C.pos(s, 0); MP.push({ s, x: p.x, y: p.y }); } }
  let x0 = 1e9, x1 = -1e9, y0 = 1e9, y1 = -1e9; MP.forEach(p => { x0 = Math.min(x0, p.x); x1 = Math.max(x1, p.x); y0 = Math.min(y0, p.y); y1 = Math.max(y1, p.y); });
  const pad = 16, k = Math.min((w - pad * 2) / (x1 - x0), (h - pad * 2) / (y1 - y0));
  const ox = (w - (x1 - x0) * k) / 2, oy = (h - (y1 - y0) * k) / 2;
  MP.forEach(p => { p.px = ox + (p.x - x0) * k; p.py = h - (oy + (p.y - y0) * k); });
  R.mk = { x0, y0, k, ox, oy };
}
const miniXY = s => { const f = ((s % C.length) + C.length) % C.length / 0.08, i = Math.min(MP.length - 1, Math.floor(f)), a = MP[i], b = MP[Math.min(MP.length - 1, i + 1)], u = f - i; return [a.px + (b.px - a.px) * u, a.py + (b.py - a.py) * u]; };
function miniNearest(e) {
  const r = mini.getBoundingClientRect(), x = (e.clientX - r.left) * (R.mw / r.width), y = (e.clientY - r.top) * (R.mh / r.height);
  let best = null, bd = 1e9; MP.forEach(p => { const d = (p.px - x) ** 2 + (p.py - y) ** 2; if (d < bd) { bd = d; best = p; } });
  return Math.sqrt(bd) < 26 ? best.s : null;
}
const _pv = new THREE.Vector3();
function screenNearest(e) {
  if (!R.ok || !MP) return null;
  const r = rc.getBoundingClientRect(), x = e.clientX - r.left, y = e.clientY - r.top; R.cam.updateMatrixWorld();
  let best = null, bd = 1e9;
  for (let i = 0; i < MP.length; i += 2) {
    const m = MP[i]; _pv.set(m.x, C.elev(m.s), -m.y).project(R.cam);
    if (_pv.z > 1 || _pv.z < -1) continue;
    const sx = (_pv.x + 1) / 2 * r.width, sy = (1 - _pv.y) / 2 * r.height, d = (sx - x) ** 2 + (sy - y) ** 2;
    if (d < bd) { bd = d; best = m; }
  }
  return best && Math.sqrt(bd) < 90 ? best.s : null;
}
mini.addEventListener('pointermove', e => { if (R.targeting && MP) R.hoverS = miniNearest(e); });
mini.addEventListener('pointerleave', () => { R.hoverS = null; });
mini.addEventListener('pointerdown', e => { if (R.targeting && MP) { const s = miniNearest(e); if (s !== null) fireItem(s); } });
function zoneCol(s) {
  const J = C.F.jump, W = C.F.wave;
  if (s >= J.s0 && s < J.s0 + J.rampLen + J.gap + J.landLen) return '#f4b400';
  if (s >= W.s0 && s <= W.s1) return '#e0a020';
  if (C.inLane(s)) return TH.cool;
  return null;
}
function drawMini(t) {
  const ctx = R.mctx; if (!ctx || !MP) return; const w = R.mw, h = R.mh;
  ctx.clearRect(0, 0, w, h); ctx.lineCap = 'round'; ctx.lineJoin = 'round';
  const seg = (s0, s1, col, lw) => { ctx.strokeStyle = col; ctx.lineWidth = lw; ctx.beginPath(); let first = true; for (let s = s0; s <= s1 + 1e-6; s += 0.08) { const [x, y] = miniXY(s); first ? ctx.moveTo(x, y) : ctx.lineTo(x, y); first = false; } ctx.stroke(); };
  seg(0, C.length - 0.09, TH.line2, 11);
  for (let i = 0; i < MP.length - 1; i++) { const zc = zoneCol(MP[i].s); if (zc) { ctx.strokeStyle = zc; ctx.lineWidth = 5; ctx.beginPath(); ctx.moveTo(MP[i].px, MP[i].py); ctx.lineTo(MP[i + 1].px, MP[i + 1].py); ctx.stroke(); } }
  const [sx, sy] = miniXY(0.02); ctx.fillStyle = TH.ink; ctx.fillRect(sx - 6, sy - 2, 12, 4);
  const zone = (sc, r, col, a) => { ctx.globalAlpha = a; seg(sc - r, sc + r, col, 13); ctx.globalAlpha = 1; };
  for (const ev of R.events) {
    if (t >= ev.t0 && t < ev.t1) {
      zone(ev.sc, ev.r, ITEMS[ev.kind].col, 0.85);
      const [x, y] = miniXY(ev.sc); ctx.fillStyle = '#fff'; ctx.font = '700 11px sans-serif'; ctx.textAlign = 'center'; ctx.fillText(ITEMS[ev.kind].name, x, y - 12);
    }
  }
  if (R.targeting && R.hoverS !== null) zone(R.hoverS, ITEMS[R.itemKind].r, ITEMS[R.itemKind].col, 0.6);
  R.cars.slice().reverse().forEach(c => {
    if (!c.st) return;
    const p = C.pos(c.st.s, c.lat || 0);
    const x = R.mk ? R.mk.ox + (p.x - R.mk.x0) * R.mk.k : miniXY(c.st.s)[0];
    const y = R.mk ? R.mh - (R.mk.oy + (p.y - R.mk.y0) * R.mk.k) : miniXY(c.st.s)[1];
    ctx.fillStyle = c.me ? TH.accent : c.color; ctx.strokeStyle = TH.ink; ctx.lineWidth = c.me ? 2.5 : 1.5;
    ctx.beginPath(); ctx.arc(x, y, c.me ? 6 : 4.5, 0, 7); ctx.fill(); ctx.stroke();
  });
}

function buildFx(ev) {
  const g = new THREE.Group(), p = C.pos(ev.sc, 0), hw = C.F.width / 2, spec = ITEMS[ev.kind];
  g.position.set(p.x, C.elev(ev.sc), -p.y); g.rotation.y = p.h;
  const mat = (col, op) => new THREE.MeshBasicMaterial({ color: new THREE.Color(col), transparent: true, opacity: op, depthWrite: false, side: THREE.DoubleSide });
  g.userData = { kind: ev.kind, parts: [] };
  if (ev.kind === 'bar') {
    for (let i = 0; i < 8; i++) { const m = new THREE.Mesh(new THREE.BoxGeometry(0.05, 0.07, hw * 2 / 8), new THREE.MeshLambertMaterial({ color: i % 2 ? 0xffffff : 0xef4444 })); m.position.set(0, 0.035, -hw + hw * 2 / 8 * (i + 0.5)); g.add(m); }
  } else {
    const box = new THREE.Mesh(new THREE.BoxGeometry(ev.r * 2, 0.16, hw * 2.2), mat(spec.col, 0.16)); box.position.y = 0.08; g.add(box); g.userData.box = box;
    if (ev.kind === 'fan') for (let i = 0; i < 10; i++) { const a = new THREE.Mesh(new THREE.ConeGeometry(0.018, 0.09, 8), mat('#bfe3ff', 0.85)); a.rotation.z = Math.PI / 2; a.userData = { u: i / 10, z: (i % 5 / 4 - 0.5) * hw * 1.6, y: 0.03 + (i % 3) * 0.04 }; g.add(a); g.userData.parts.push(a); }
    else for (let i = 0; i < 3; i++) { const rg = new THREE.Mesh(new THREE.TorusGeometry(hw * 1.1, 0.012, 8, 40), mat('#c4b5fd', 0.9)); rg.rotation.x = Math.PI / 2; rg.position.y = 0.02; rg.userData = { u: i / 3 }; g.add(rg); g.userData.parts.push(rg); }
  }
  g.userData.ev = ev; return g;
}
function spawnFx(ev) {
  if (!R.ok) return;
  const fx = buildFx(ev); R.fxs.push(fx); R.scene.add(fx);
}
function updAimFx() {
  if (!R.ok) return;
  const want = R.targeting && R.hoverS !== null && R.itemKind ? R.hoverS : null;
  if (want === null) { if (R.aimFx) R.aimFx.visible = false; R.aimS = null; return; }
  if (R.aimS !== want || R.aimKind !== R.itemKind || !R.aimFx) {
    if (R.aimFx) { R.scene.remove(R.aimFx); disposeGroup(R.aimFx); }
    const g = buildFx({ kind: R.itemKind, sc: want, r: ITEMS[R.itemKind].r });
    g.userData.parts.forEach(a => { a.visible = false; });
    g.traverse(o => { if (o.material) { o.material.transparent = true; o.material.opacity = o === g.userData.box ? 0.4 : 0.6; } });
    R.aimFx = g; R.aimS = want; R.aimKind = R.itemKind; R.scene.add(g);
  }
  R.aimFx.visible = true;
}
function killFx() {
  for (const fx of R.fxs) { R.scene.remove(fx); disposeGroup(fx); }
  R.fxs = [];
}
function updFx(t, ts) {
  const hw = C.F.width / 2;
  for (const g of R.fxs) {
    const ev = g.userData.ev, on = t >= ev.t0 && t < ev.t1; g.visible = on; if (!on) continue;
    if (ev.kind === 'fan') g.userData.parts.forEach(a => { const f = (a.userData.u + (t * 1.8)) % 1; a.position.set(ev.r * (0.95 - f * 1.9), a.userData.y, a.userData.z); });
    else if (ev.kind === 'mag') { g.userData.parts.forEach(rg => { const f = (rg.userData.u + t * 1.2) % 1; rg.scale.setScalar(1.25 - f); rg.material.opacity = 0.9 * (1 - f); }); g.userData.box.material.opacity = 0.12 + 0.08 * Math.sin(ts / 80); }
  }
}

function applyOnlineEvent(ev, isMine) {
  R.events.push(ev);
  R.cars.forEach(c => { c.sim = T.simulate(c.car, LAPS, R.events); });
  R.endAt = Math.max(...R.cars.map(endTime));
  spawnFx(ev);
  SFX.item(ev.kind);
  const spec = ITEMS[ev.kind];
  toast((isMine ? '' : R.raceMode === 'cpu' ? 'CPUが ' : '相手が ') + spec.name + ' 発動！');
}
function fireItem(sc) {
  if (R.raceMode !== 'cpu' && R.p2pRule === 'off') return;
  if (!R.itemKind) return;
  const kind = R.itemKind, spec = ITEMS[kind], t0 = Math.max(0, R.t);
  const ev = { kind, id: R.events.length + 1, t0, t1: t0 + 1.0, sc, r: spec.r, dir: 1, seed: Math.random() };
  R.used = true; R.targeting = false; R.hoverS = null;
  applyOnlineEvent(ev, true);
  if (R.raceMode !== 'cpu' && NET.connected) sendP2P({ type: 'fire_item', ev });
  updItemUi();
}
function resetItem() { SFX.stopMotor(); R.used = false; R.targeting = false; R.events = []; R.cpuPlan = null; R.prevAir = false; R.hoverS = null; R.aimS = null; if (R.aimFx) R.aimFx.visible = false; killFx(); R.cars.forEach(c => { c.sim = c.baseSim; c.crashedSfx = false; }); if (R.cars.length) R.endAt = Math.max(...R.cars.map(endTime)); }
function itemReportHTML() {
  if (!R.events.length) return '';
  const ev = R.events[R.events.length - 1], k = ev.kind;
  const why = c => k === 'fan' ? `車重 ${c.an.mass.toFixed(0)}g` : k === 'mag' ? `ブロック ${c.an.blocks}個・鉄 ${(c.an.mHeavy || 0).toFixed(0)}g` : `先端の尖り ${Math.round(c.an.nose * 100)}%`;
  const rows = R.cars.map(c => {
    const it = c.sim.stats.item, base = c.baseSim; let res;
    if (c.sim.dnf && !base.dnf) res = '<span style="color:var(--bad)">× ' + WHY[c.sim.dnf.reason] + '</span>';
    else if (it && !it.hit) res = '範囲を通らず影響なし';
    else if (c.sim.finish !== null && base.finish !== null) { const d = c.sim.finish - base.finish; res = d < 0.05 ? 'ほぼ影響なし' : '<strong>+' + d.toFixed(2) + '秒</strong>のロス'; }
    else res = '影響なし';
    return `<li><strong>${c.name}</strong>：${res} <span class="small">（${why(c)}）</span></li>`;
  }).join('');
  return `<b>おじゃま「${ITEMS[k].name}」の結果</b><ul>${rows}</ul>`;
}

/* ---- タブ ---- */
function updTabs() {
  const ok = S.an.rules.ok;
  $('tabR').classList.toggle('disabled', !ok);
  $('tabR').disabled = false;
}
function notifyRuleNg() {
  SFX.error();
  const a = S.an;
  const why = !a.rules.weightMin ? `車重が軽すぎます（${a.mass.toFixed(1)}g / 70g以上にしてください）`
    : !a.rules.weightMax ? `重量オーバーです（${a.mass.toFixed(1)}g / 140g以下にしてください）`
    : !a.rules.connected ? `浮いているブロックが${a.floatCells.length}個あります（フレームにつなげてください）`
    : '車検（重量70〜140g・全パーツ接続）を通すと出走できます';
  toast('⚠️ ' + why);
  const ins = $('inspect');
  if (ins) ins.classList.remove('collapsed-mobile');
}
function showTab(which) {
  SFX.stopMotor(); SFX.click();
  const g = which === 'g';
  $('garage').hidden = !g; $('race').hidden = g;
  $('app').classList.add('fit'); $('hdrTools').hidden = !g;
  document.body.classList.toggle('in-race', !g); setAero(false);
  $('tabG').setAttribute('aria-selected', String(g)); $('tabR').setAttribute('aria-selected', String(!g));
  if (g) {
    layout3d(); markDirty();
    if (isMobileScreen() && !V.fp) toggleFP(true);
  } else {
    enterRace();
    if (document.body.classList.contains('mob')) setRaceSheet(true);
  }
  window.scrollTo({ top: 0 });
}
$('tabG').onclick = () => showTab('g');
$('tabR').onclick = () => { if (S.an.rules.ok) showTab('r'); else notifyRuleNg(); };
$('goRace').onclick = () => { if (S.an.rules.ok) showTab('r'); else notifyRuleNg(); };
function applyMob() {
  const mob = isMobileScreen(), was = document.body.classList.contains('mob');
  document.body.classList.toggle('mob', mob);
  if (was !== mob) { if (!mob) { setAero(false); $('race').classList.remove('sheet-open'); } updTouchUi(); updStartBtn(); updItemUi(); }
}
function onResize() { applyMob(); if (!$('garage').hidden) { layout3d(); } else { layoutRace(); } }
/* 風洞データ（スマホではシート表示） */
function setAero(open) {
  document.body.classList.toggle('aero-open', !!open);
  const b = $('bAero'); if (b) b.setAttribute('aria-expanded', String(!!open));
}
if ($('bAero')) $('bAero').onclick = e => { e.stopPropagation(); SFX.click(); setAero(!document.body.classList.contains('aero-open')); };
if ($('bAeroClose')) $('bAeroClose').onclick = () => setAero(false);
document.addEventListener('pointerdown', e => {
  if (!document.body.classList.contains('aero-open')) return;
  if (e.target.closest('.g-side') || e.target.closest('#bAero')) return;
  setAero(false);
}, true);
/* 全画面 (Fullscreen API が使える端末のみ) */
{
  const fb = $('bFull'), de = document.documentElement;
  const req = de.requestFullscreen || de.webkitRequestFullscreen;
  if (fb && req && (document.fullscreenEnabled || document.webkitFullscreenEnabled)) {
    fb.hidden = false;
    const isFs = () => !!(document.fullscreenElement || document.webkitFullscreenElement);
    fb.onclick = () => {
      SFX.click();
      try {
        if (isFs()) (document.exitFullscreen || document.webkitExitFullscreen).call(document);
        else { const r = req.call(de, { navigationUI: 'hide' }); if (r && r.catch) r.catch(() => toast('この端末では全画面にできませんでした')); }
      } catch (_) { toast('この端末では全画面にできませんでした'); }
    };
    const sync = () => { fb.textContent = isFs() ? '⤢' : '⛶'; fb.title = isFs() ? '全画面を解除' : '全画面表示'; setTimeout(onResize, 120); };
    document.addEventListener('fullscreenchange', sync); document.addEventListener('webkitfullscreenchange', sync);
  }
}
window.addEventListener('resize', onResize);
if (window.ResizeObserver) {
  new ResizeObserver(onResize).observe(document.querySelector('.app'));
  if ($('v3wrap')) new ResizeObserver(onResize).observe($('v3wrap'));
}

/* ===== 起動 ===== */
readTheme();
{ const p = PRE.find(x => x.id === 'std'); S.g = p.fn(); $('presetNote').textContent = p.name + '：' + p.note; }
applyMob();
init3d(); init3dRace();
changed(); updUndo(); renderSlots(); layout3d();
updTouchUi();
if (isMobileScreen()) toggleFP(true);
if (document.fonts && document.fonts.ready) document.fonts.ready.then(markDirty);
requestAnimationFrame(loopEd); requestAnimationFrame(loopRace);
})();