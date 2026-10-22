#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
FPL Assistant - a local Fantasy Premier League helper
=====================================================
Reads the same live data the official FPL website/app uses (every player's price,
form, injuries, fixtures, price-change meter, and your own team) and gives you:

  * Build a Team    - the best 15-man squad for a budget (new team, Wildcard, Free Hit)
  * My Team         - transfer suggestions for your existing team, captain picks, alerts
  * Chips           - when to play Wildcard, Free Hit, Bench Boost and Triple Captain
  * Players & Prices- every player with live price + the official price-change meter
  * Fixtures        - difficulty grid with blank/double gameweeks highlighted

How to run:   python fpl_assistant.py
Then open     http://localhost:8765   (it opens automatically)
Use it on your phone (same Wi-Fi):    python fpl_assistant.py --share   (prints an address to open on the phone,
                                       then 'Add to Home Screen' in Safari/Chrome)
Put it online (e.g. a free Render web service): start command  python fpl_assistant.py  - it picks up the
                                       host's PORT setting by itself and works from any phone.
Try it without internet or a team ID:  python fpl_assistant.py --demo   (fake players, for a look around)
Needs Python 3.8 or newer. Nothing to install. Your team ID is only used to read
your public FPL page; nothing is sent anywhere except fantasy.premierleague.com.

The advice is a projection model, not a crystal ball. It cannot press buttons in
the FPL app for you - you make the moves there.
"""

import argparse
import gzip
import json
import math
import os
import random
import re
import socket
import ssl
import struct
import sys
import threading
import time
import traceback
import webbrowser
import zlib
from collections import Counter, defaultdict
from datetime import datetime, timedelta, timezone
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from urllib.error import HTTPError, URLError
from urllib.parse import parse_qs, urlparse
from urllib.request import Request, urlopen

API_ROOT = "https://fantasy.premierleague.com/api/"
USER_AGENT = ("Mozilla/5.0 (Windows NT 10.0; Win64; x64) AppleWebKit/537.36 "
              "(KHTML, like Gecko) Chrome/124.0 Safari/537.36")

POS_NAMES = {1: "GKP", 2: "DEF", 3: "MID", 4: "FWD"}
HIT_COST = 4            # points lost per extra transfer
EFFORT = 1.0            # scales how hard the squad search tries (lowered on slow free web hosts)
BENCH_WEIGHT = 0.12     # how much a bench player's points count when picking a squad
PRIOR_MINUTES = 450.0   # how strongly we pull a player's rate towards a price-based guess
FDR_MULT = {1: 1.30, 2: 1.15, 3: 1.00, 4: 0.88, 5: 0.75}
VAR_SHARE = {1: 0.60, 2: 0.70, 3: 0.60, 4: 0.60}   # share of a player's points that depends on the fixture
GOAL_PTS = {1: 10, 2: 6, 3: 5, 4: 4}
MONTHS = {"jan": 1, "feb": 2, "mar": 3, "apr": 4, "may": 5, "jun": 6,
          "jul": 7, "aug": 8, "sep": 9, "oct": 10, "nov": 11, "dec": 12}
CHIP_LABEL = {"wildcard": "Wildcard", "freehit": "Free Hit", "bboost": "Bench Boost",
              "3xc": "Triple Captain", "manager": "Assistant Manager"}
CHIP_ORDER = ["wildcard", "freehit", "bboost", "3xc"]


PAGE = r'''<!doctype html>
<html lang="en">
<head>
<meta charset="utf-8">
<meta name="viewport" content="width=device-width, initial-scale=1, viewport-fit=cover">
<meta name="theme-color" content="#3d0a4f">
<meta name="apple-mobile-web-app-capable" content="yes">
<meta name="mobile-web-app-capable" content="yes">
<meta name="apple-mobile-web-app-title" content="FPL Assistant">
<meta name="apple-mobile-web-app-status-bar-style" content="default">
<link rel="manifest" href="/manifest.webmanifest">
<link rel="apple-touch-icon" href="/icon.png">
<link rel="icon" href="/icon.png" type="image/png">
<title>FPL Assistant</title>
<style>
:root{--bg:#f4f5fa;--card:#fff;--ink:#181a2e;--muted:#697089;--line:#e1e4ee;--brand:#3d0a4f;--brand2:#7a2cf0;--ok:#0a9b5a;--bad:#d4283d;--warn:#c27c00;--soft:#eef0f8;--pitch1:#1f8a4c;--pitch2:#2a9d5c}
@media(prefers-color-scheme:dark){:root{--bg:#10111b;--card:#1a1b2b;--ink:#eceef8;--muted:#9a9fba;--line:#2b2d44;--brand:#d3b5ff;--brand2:#9b6bff;--ok:#38d68e;--bad:#ff6f82;--warn:#ffbf4a;--soft:#25263c;--pitch1:#17653a;--pitch2:#1d7a47}}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--ink);font:15px/1.45 system-ui,-apple-system,"Segoe UI",Roboto,sans-serif}
.wrap{max-width:1100px;margin:0 auto;padding:0 14px}
header{background:var(--card);border-bottom:1px solid var(--line);position:sticky;top:0;z-index:5}
.top{display:flex;gap:12px;align-items:center;flex-wrap:wrap;padding:10px 0}
h1{font-size:19px;margin:0;color:var(--brand)}
#status{color:var(--muted);font-size:13px;flex:1;min-width:200px}
.demo{background:var(--warn);color:#fff;border-radius:6px;padding:1px 7px;font-size:12px;font-weight:700;margin-right:6px}
button,select,input{font:inherit;color:inherit}
button{cursor:pointer;border:1px solid var(--line);background:var(--soft);border-radius:8px;padding:6px 11px}
button:hover{border-color:var(--brand2)}
button.primary{background:var(--brand2);border-color:var(--brand2);color:#fff;font-weight:600}
input,select{border:1px solid var(--line);background:var(--card);border-radius:8px;padding:6px 9px}
input[type=number]{width:88px}
.ctrl{display:flex;gap:10px;align-items:center;flex-wrap:wrap;padding:0 0 10px}
.ctrl label{color:var(--muted);font-size:13px}
nav.tabs{display:flex;gap:2px;overflow-x:auto}
nav.tabs button{border:0;border-bottom:3px solid transparent;background:none;border-radius:0;padding:9px 13px;color:var(--muted);white-space:nowrap}
nav.tabs button.on{color:var(--brand);border-bottom-color:var(--brand2);font-weight:700}
main{padding:16px 14px 60px}
section{display:none}section.on{display:block}
.card{background:var(--card);border:1px solid var(--line);border-radius:12px;padding:14px;margin-bottom:14px}
.card h2{margin:0 0 8px;font-size:16px}
.muted{color:var(--muted)}.small{font-size:13px}
.grid{display:grid;gap:10px;grid-template-columns:repeat(auto-fit,minmax(150px,1fr))}
.stat{background:var(--soft);border-radius:10px;padding:9px 11px}
.stat b{display:block;font-size:19px}.stat span{color:var(--muted);font-size:12px}
.busy{padding:26px;text-align:center;color:var(--muted)}
.spin{display:inline-block;width:15px;height:15px;border:2px solid var(--line);border-top-color:var(--brand2);border-radius:50%;animation:sp .8s linear infinite;vertical-align:-3px;margin-right:8px}
@keyframes sp{to{transform:rotate(360deg)}}
.err{background:rgba(212,40,61,.1);border:1px solid var(--bad);color:var(--ink);border-radius:10px;padding:12px}
.empty{padding:30px;text-align:center;color:var(--muted)}
.pitch{background:linear-gradient(var(--pitch1),var(--pitch2));border-radius:12px;padding:12px 6px;display:flex;flex-direction:column;gap:10px}
.prow{display:flex;justify-content:center;gap:8px;flex-wrap:wrap}
.bench{display:flex;gap:8px;flex-wrap:wrap;justify-content:center;align-items:center;margin-top:10px;padding:8px;background:var(--soft);border-radius:12px}
.bench .lbl{font-weight:700;color:var(--muted);font-size:12px;text-transform:uppercase;margin-right:6px}
.pc{position:relative;width:104px;background:var(--card);border-radius:10px;padding:6px 5px 5px;text-align:center;box-shadow:0 1px 3px rgba(0,0,0,.25)}
.pc.hurt{outline:2px solid var(--warn)}
.pc .nm{font-weight:700;font-size:13px;white-space:nowrap;overflow:hidden;text-overflow:ellipsis}
.pc .sub{font-size:11px;color:var(--muted)}.pc .xp{font-size:15px;font-weight:800;color:var(--brand2)}
.pc .fxr{display:flex;justify-content:center;gap:2px;flex-wrap:wrap;margin-top:2px}
.gwcell{display:inline-flex;gap:1px}
.fx{display:inline-block;min-width:22px;padding:0 3px;border-radius:4px;font-size:10px;font-weight:700;text-align:center;line-height:16px}
.f0{background:var(--soft);color:var(--muted)}.f1{background:#0b7a43;color:#fff}.f2{background:#1f9d57;color:#fff}.f3{background:#c9ccd9;color:#222}.f4{background:#ef8a22;color:#fff}.f5{background:#d4283d;color:#fff}
.cap{position:absolute;top:-6px;left:-6px;background:#111;color:#fff;border-radius:50%;width:19px;height:19px;font-size:11px;line-height:19px}
.cap.v{background:#666}
.flag{position:absolute;top:-6px;right:-6px;background:var(--warn);color:#fff;border-radius:9px;padding:0 5px;font-size:10px;font-style:normal;font-weight:700;line-height:17px}
.flag.s-i,.flag.s-s,.flag.s-u{background:var(--bad)}
.tr{position:absolute;bottom:42px;right:4px;font-size:10px;font-style:normal}.tr.up{color:var(--ok)}.tr.dn{color:var(--bad)}
.tag{display:inline-block;border-radius:6px;padding:1px 8px;font-size:12px;font-weight:700;background:var(--soft);color:var(--muted)}
.tag.ok{background:rgba(10,155,90,.15);color:var(--ok)}.tag.bad{background:rgba(212,40,61,.14);color:var(--bad)}.tag.warn{background:rgba(217,138,0,.16);color:var(--warn)}
.move{display:flex;gap:10px;align-items:flex-start;padding:9px 0;border-top:1px solid var(--line);flex-wrap:wrap}
.move:first-child{border-top:0}
.who{flex:1;min-width:210px}.who b{font-size:15px}.arrow{font-size:20px;color:var(--muted);align-self:center}
.gain{font-weight:800;color:var(--ok);align-self:center;min-width:64px;text-align:right}
ul.why{margin:3px 0 0 16px;padding:0;color:var(--muted);font-size:12.5px}
table{border-collapse:collapse;width:100%}
th,td{padding:6px 8px;border-bottom:1px solid var(--line);text-align:left;vertical-align:middle;font-size:13.5px}
th{color:var(--muted);font-size:12px;text-transform:uppercase;white-space:nowrap}
td.n,th.n{text-align:right}
.scroll{overflow-x:auto}
details{border:1px solid var(--line);border-radius:10px;padding:8px 12px;margin-top:8px}
summary{cursor:pointer;font-weight:600}
.chips4{display:grid;gap:12px;grid-template-columns:repeat(auto-fit,minmax(250px,1fr))}
.chipc{border:1px solid var(--line);border-radius:12px;padding:12px;background:var(--card)}
.chipc h3{margin:0 0 4px;font-size:16px;display:flex;justify-content:space-between;align-items:center;gap:6px}
.opt{font-size:13px;padding:5px 0;border-top:1px dashed var(--line)}
.opt.star{font-weight:600}
.meter{display:inline-block;width:70px;height:8px;background:var(--soft);border-radius:4px;position:relative;vertical-align:middle}
.meter i{position:absolute;top:0;bottom:0;border-radius:4px}
.meter i.p{left:50%;background:var(--ok)}.meter i.m{right:50%;background:var(--bad)}
.meter:after{content:"";position:absolute;left:50%;top:-2px;bottom:-2px;width:1px;background:var(--muted)}
.two{display:grid;gap:14px;grid-template-columns:repeat(auto-fit,minmax(300px,1fr))}
.filters{display:flex;gap:8px;flex-wrap:wrap;margin-bottom:10px;align-items:center}
.grid-fx td{padding:4px 5px;text-align:center;white-space:nowrap}.grid-fx td:first-child,.grid-fx th:first-child{text-align:left;position:sticky;left:0;background:var(--card)}
.sp-b{background:rgba(212,40,61,.12)}.sp-d{background:rgba(10,155,90,.12)}
footer{color:var(--muted);font-size:12px;margin-top:18px}
@media(max-width:560px){.prow{gap:4px}.pitch{padding:10px 4px}.pc{width:66px;padding:5px 2px}.pc .nm{font-size:11px}.pc .sub{font-size:10px}.pc .xp{font-size:14px}.fx{min-width:17px;font-size:8px;padding:0 2px}.cap{width:17px;height:17px;line-height:17px;font-size:10px}.bench{gap:4px}}
.sm{display:none}
[hidden]{display:none!important}
.phonebar{background:var(--soft);border-radius:8px;padding:6px 10px;margin:0 0 10px;font-size:13px}
@media(max-width:700px){
  header{position:static;padding-top:env(safe-area-inset-top)}
  .top{padding:8px 0 4px;gap:8px}
  #status{font-size:12px;min-width:0;order:3;flex-basis:100%}
  .ctrl .hint{display:none}
  input,select{font-size:16px}
  nav.tabs{position:fixed;left:0;right:0;bottom:0;z-index:30;background:var(--card);border-top:1px solid var(--line);padding:0 0 env(safe-area-inset-bottom);overflow:visible}
  nav.tabs button{flex:1;border-bottom:0;border-top:3px solid transparent;padding:10px 2px 9px;font-size:12px;text-align:center}
  nav.tabs button.on{border-top-color:var(--brand2)}
  .lg{display:none}.sm{display:inline}
  main{padding-bottom:90px}
}
</style>
</head>
<body>
<header>
  <div class="wrap">
    <div class="top">
      <h1>FPL Assistant</h1>
      <div id="status">Loading live data...</div>
      <button id="refresh" title="Download the latest prices, injuries and fixtures from FPL">Refresh data</button>
    </div>
    <div class="ctrl">
      <label>Your FPL team ID <input id="tid" inputmode="numeric" placeholder="e.g. 1234567" size="10"></label>
      <label>Look ahead <select id="hor"><option value="1">1 gameweek</option><option value="3">3 gameweeks</option><option value="5" selected>5 gameweeks</option><option value="8">8 gameweeks</option><option value="10">10 gameweeks</option></select></label>
      <button class="primary" id="load">Load my team</button>
      <span class="small muted hint">Find your ID in the address of your Points page: fantasy.premierleague.com/entry/<b>1234567</b>/event/7</span>
    </div>
    <div id="phonebar" class="phonebar" hidden></div>
    <nav class="tabs" id="tabs">
      <button data-tab="team" class="on">My Team</button>
      <button data-tab="chips">Chips</button>
      <button data-tab="build"><span class="lg">Build a Team</span><span class="sm">Build</span></button>
      <button data-tab="players"><span class="lg">Players &amp; Prices</span><span class="sm">Prices</span></button>
      <button data-tab="fixtures">Fixtures</button>
    </nav>
  </div>
</header>
<main class="wrap">
  <section id="tab-team" class="on"><div id="team-out" class="empty">Enter your team ID above and press <b>Load my team</b>.</div></section>
  <section id="tab-chips"><div id="chips-out" class="empty">Enter your team ID above, then open this tab to see when to play your chips.</div></section>
  <section id="tab-build">
    <div class="card">
      <h2>Build the best squad</h2>
      <p class="muted small" style="margin-top:0">Picks 15 players (2 GK, 5 DEF, 5 MID, 3 FWD, max 3 per club) that maximise projected points over the look-ahead you chose, using today's live prices. Use it for a brand-new team, a Wildcard, or a Free Hit (set look-ahead to 1).</p>
      <div class="filters">
        <label>Budget (&pound;m) <input id="budget" type="number" step="0.1" min="60" max="200" value="100.0"></label>
        <button class="primary" id="build">Build squad</button>
        <button id="usemine" title="Budget = your squad's selling value + bank (what a Wildcard or Free Hit gives you)">Use my team's budget</button>
      </div>
    </div>
    <div id="build-out"></div>
  </section>
  <section id="tab-players">
    <div class="card">
      <div class="filters">
        <input id="q" placeholder="Search player..." size="16">
        <select id="fpos"><option value="0">All positions</option><option value="1">GKP</option><option value="2">DEF</option><option value="3">MID</option><option value="4">FWD</option></select>
        <select id="fteam"><option value="">All clubs</option></select>
        <label class="small muted">Max price <input id="fmax" type="number" step="0.1" value="15" min="3.5"></label>
        <label class="small muted"><input type="checkbox" id="favail" checked> hide unavailable</label>
        <select id="fsort"><option value="xh">Sort: projected points</option><option value="x1">Sort: next gameweek</option><option value="c">Sort: price</option><option value="f">Sort: form</option><option value="o">Sort: ownership</option><option value="tp">Sort: total points</option><option value="pj">Sort: price meter (risers)</option></select>
      </div>
      <div id="pl-table"></div>
    </div>
    <div class="two" id="pw"></div>
  </section>
  <section id="tab-fixtures"><div id="fx-out"></div></section>
  <footer>Projections are estimates from official FPL data, not guarantees. This app only reads data; make your moves in the FPL app or website.
    <details><summary>How are points projected?</summary>
      <ul class="why">
        <li>Each player's points per 90 minutes this season, pulled towards a price-based guess when he has played little.</li>
        <li>Goals and assists are compared with expected goals/assists (xG/xA) to soften lucky or unlucky runs, and recent form gets a small say.</li>
        <li>Expected minutes come from how much he has played, plus injury news and the chance of playing from FPL.</li>
        <li>Each fixture is scaled by FPL's difficulty rating blended with how many chances each club creates and allows this season. Double gameweeks add up; blank gameweeks score zero.</li>
        <li>Squads are chosen to maximise the best XI plus the captain's double, with a little credit for bench cover. A transfer hit costs 4 points, and hits need a clear margin before they are recommended.</li>
      </ul>
    </details>
  </footer>
</main>
<script>
'use strict';
const S = {id: localStorage.getItem('fpl_id') || '', ft: null, team: null, status: null, players: null, loaded: {}};
const $ = (s, r) => (r || document).querySelector(s);
const esc = s => String(s == null ? '' : s).replace(/[&<>"']/g, c => ({'&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'}[c]));
const money = t => '\u00a3' + (t / 10).toFixed(1) + 'm';
const POS = {1: 'GKP', 2: 'DEF', 3: 'MID', 4: 'FWD'};
const horizon = () => $('#hor').value;

async function api(path, params, fresh) {
  const q = new URLSearchParams();
  for (const k in (params || {})) { const v = params[k]; if (v !== null && v !== undefined && v !== '') q.set(k, v); }
  if (fresh) q.set('fresh', '1');
  let res;
  try { res = await fetch(path + '?' + q.toString()); }
  catch (e) { throw new Error("Can't reach the app's local server. Is the terminal window still running?"); }
  let data;
  try { data = await res.json(); } catch (e) { throw new Error('Unexpected reply from the app.'); }
  if (!res.ok) throw new Error(data.error || ('Error ' + res.status));
  return data;
}
const busy = (el, msg) => { el.className = ''; el.innerHTML = '<div class="busy"><span class="spin"></span>' + esc(msg) + '</div>'; };
const fail = (el, e) => { el.className = ''; el.innerHTML = '<div class="err"><b>Couldn\'t do that.</b> ' + esc(e.message || e) + '</div>'; };
const fmtDate = iso => new Date(iso).toLocaleString([], {weekday: 'short', day: 'numeric', month: 'short', hour: '2-digit', minute: '2-digit'});
function fmtDur(ms) {
  if (ms <= 0) return 'now';
  const m = Math.floor(ms / 60000), d = Math.floor(m / 1440), h = Math.floor((m % 1440) / 60);
  return d ? d + 'd ' + h + 'h' : h ? h + 'h ' + (m % 60) + 'm' : (m % 60) + 'm';
}

/* ---------- small building blocks ---------- */
const fxTag = f => '<span class="fx f' + f.d + '" title="' + (f.h ? 'Home' : 'Away') + ' vs ' + esc(f.o) + ', difficulty ' + f.d + '">' + esc(f.h ? f.o : f.o.toLowerCase()) + '</span>';
function fxCells(fx, n) {
  return fx.slice(0, n || 3).map(g => '<span class="gwcell">' + (g.length ? g.map(fxTag).join('') : '<span class="fx f0">-</span>') + '</span>').join('');
}
function pcard(c, role) {
  const flag = c.status !== 'a' || (c.chance != null && c.chance < 100);
  const b = role === 'C' ? '<b class="cap">C</b>' : role === 'V' ? '<b class="cap v">V</b>' : '';
  const w = flag ? '<i class="flag s-' + esc(c.status) + '" title="' + esc(c.news) + '">' + (c.status === 'a' ? '!' : esc(c.status.toUpperCase())) + '</i>' : '';
  const tr = c.pc == null ? '' : (c.pc >= 80 ? '<i class="tr up" title="Price about to rise">&#9650;</i>' : c.pc <= -80 ? '<i class="tr dn" title="Price about to fall">&#9660;</i>' : '');
  return '<div class="pc' + (flag ? ' hurt' : '') + '">' + b + w + tr + '<div class="nm" title="' + esc(c.name) + '">' + esc(c.name) + '</div><div class="sub">' + esc(c.team) + ' \u00b7 ' + money(c.price) +
    '</div><div class="xp">' + c.xp1.toFixed(1) + '</div><div class="fxr">' + fxCells(c.fx, 3) + '</div></div>';
}
function pitch(d) {
  const by = {}; d.squad.forEach(c => { by[c.id] = c; });
  const rows = {1: [], 2: [], 3: [], 4: []};
  d.xi.forEach(id => rows[by[id].pos].push(by[id]));
  const role = id => id === d.captain ? 'C' : id === d.vice ? 'V' : '';
  const line = a => '<div class="prow">' + a.map(c => pcard(c, role(c.id))).join('') + '</div>';
  return '<div class="pitch">' + line(rows[1]) + line(rows[2]) + line(rows[3]) + line(rows[4]) + '</div><div class="bench"><span class="lbl">Bench</span>' +
    d.bench.map(id => pcard(by[id], '')).join('') + '</div><p class="small muted">Big number = projected points next gameweek. Coloured boxes = next fixtures (CAPITALS home, lowercase away; green easy, red hard).</p>';
}
function stat(label, value) { return '<div class="stat"><b>' + value + '</b><span>' + label + '</span></div>'; }

/* ---------- header status ---------- */
async function loadStatus(fresh) {
  try {
    S.status = await api('/api/status', {}, fresh);
    drawStatus();
  } catch (e) {
    $('#status').innerHTML = '<span style="color:var(--bad)">' + esc(e.message) + '</span>';
  }
}
function drawStatus() {
  const s = S.status; if (!s) return;
  const pb = $('#phonebar');
  if (s.phone_url && (location.hostname === 'localhost' || location.hostname === '127.0.0.1')) {
    pb.hidden = false;
    pb.innerHTML = 'On your phone (same Wi-Fi) open <b>' + esc(s.phone_url) + '</b>, then Share &rarr; Add to Home Screen (iPhone) or menu &rarr; Add to Home screen (Android).';
  } else { pb.hidden = true; }
  const next = (s.price_deadlines || []).map(d => new Date(d)).find(d => d > new Date());
  $('#status').innerHTML = (s.mode === 'demo' ? '<span class="demo">DEMO DATA</span>' : '') +
    '<b>GW' + s.gw_next + '</b> deadline in <b>' + fmtDur(new Date(s.deadline) - new Date()) + '</b> &middot; ' + s.players + ' players &middot; data fetched ' +
    new Date(s.fetched_at * 1000).toLocaleTimeString([], {hour: '2-digit', minute: '2-digit'}) +
    (next ? ' &middot; next price change ' + fmtDate(next.toISOString()) : '');
}
setInterval(drawStatus, 60000);

/* ---------- My Team ---------- */
function movesHtml(p) {
  if (!p.moves.length) return '<p class="muted" style="margin:6px 0 0">No transfers: keep your squad and bank the free transfer.</p>';
  return p.moves.map(mv => '<div class="move"><div class="who"><span class="tag bad">OUT</span> <b>' + esc(mv.out.name) + '</b> <span class="muted small">' + esc(mv.out.team) + ' &middot; sells for ' + money(mv.out.sell) +
    '</span><ul class="why">' + mv.why_out.map(w => '<li>' + esc(w) + '</li>').join('') + '</ul></div><div class="arrow">&rarr;</div><div class="who"><span class="tag ok">IN</span> <b>' + esc(mv.in.name) + '</b> <span class="muted small">' + esc(mv.in.team) + ' &middot; ' + money(mv.in.price) +
    ' &middot; ' + mv.in.xph.toFixed(1) + ' pts projected</span><div class="fxr" style="margin-top:3px;justify-content:flex-start">' + fxCells(mv.in.fx, 5) + '</div><ul class="why">' + mv.why_in.map(w => '<li>' + esc(w) + '</li>').join('') + '</ul></div><div class="gain">+' + mv.gain.toFixed(1) + '</div></div>').join('');
}
function planTitle(p) {
  if (!p.k) return 'Roll (no transfers)';
  return p.k + ' transfer' + (p.k > 1 ? 's' : '') + (p.hits ? ' (' + p.hits + ' hit' + (p.hits > 1 ? 's' : '') + ', -' + p.hit_cost + ' pts)' : ' (free)');
}
function renderTeam(d) {
  const rec = d.plans.find(p => p.k === d.recommended) || d.plans[0];
  const out = $('#team-out');
  let h = '<div class="card"><h2>' + esc(d.team_name || 'Your team') + ' <span class="muted small">' + esc(d.manager) + (d.overall_rank ? ' &middot; overall rank ' + Number(d.overall_rank).toLocaleString() : '') + '</span></h2><div class="grid">' +
    stat('In the bank', money(d.bank)) + stat('Squad selling value', money(d.value)) +
    '<div class="stat"><b><input type="number" id="ft" min="0" max="5" value="' + d.ft + '" style="width:62px"></b><span>Free transfers ' + (d.ft_estimated ? '(estimated - edit if wrong)' : '') + '</span></div>' +
    stat('Projected next ' + d.horizon + ' GW' + (d.horizon > 1 ? 's' : ''), d.xp_now.toFixed(0) + ' pts') + '</div>';
  if (d.made_next) h += '<p class="small muted">You have already made ' + d.made_next + ' transfer(s) for GW' + d.gw_next + '. They are included below.</p>';
  h += '</div>';
  h += '<div class="card"><h2>Recommended for GW' + d.gw_next + ': ' + planTitle(rec) + '</h2>';
  if (rec.k) h += '<p class="muted small" style="margin-top:0">Expected gain over the next ' + d.horizon + ' gameweek(s): <b>+' + rec.gain.toFixed(1) + ' pts</b>' + (rec.hit_cost ? ', minus ' + rec.hit_cost + ' for hits = <b>+' + rec.net.toFixed(1) + ' net</b>' : '') + '. Bank afterwards: ' + money(rec.bank_after) + '.</p>';
  else h += '<p class="muted small" style="margin-top:0">No move is clearly worth using a transfer on this week.</p>';
  h += movesHtml(rec);
  h += d.plans.filter(p => p !== rec).map(p => '<details><summary>' + planTitle(p) + ' &mdash; ' + (p.k ? 'gain +' + p.gain.toFixed(1) + ', net ' + (p.net >= 0 ? '+' : '') + p.net.toFixed(1) : 'baseline') + '</summary>' + movesHtml(p) + '</details>').join('');
  h += '</div>';
  if (d.alerts.length) h += '<div class="card"><h2>Injury &amp; availability alerts</h2>' + d.alerts.map(a => '<div class="small" style="margin:3px 0"><span class="tag ' + (a.status === 'a' || a.status === 'd' ? 'warn' : 'bad') + '">' + esc((a.status || '').toUpperCase()) + '</span> <b>' + esc(a.name) + '</b> ' + esc(a.news || (a.chance != null ? a.chance + '% chance of playing' : '')) + '</div>').join('') + '</div>';
  h += '<div class="card"><h2>Captain picks for GW' + d.gw_next + '</h2><div class="prow" style="justify-content:flex-start">' + d.captains.map((c, i) => pcard(c, i === 0 ? 'C' : i === 1 ? 'V' : '')).join('') + '</div></div>';
  h += '<div class="card"><h2>Your squad (best XI for the next ' + d.horizon + ' GW' + (d.horizon > 1 ? 's' : '') + ', ' + esc(d.formation) + ')</h2>' + pitch(d) + '</div>';
  out.className = ''; out.innerHTML = h;
  $('#ft').addEventListener('change', e => { S.ft = e.target.value === '' ? null : e.target.value; loadTeam(); });
}
async function loadTeam(fresh) {
  const id = $('#tid').value.trim();
  if (!/^\d+$/.test(id)) { fail($('#team-out'), new Error('Your team ID should be a number, e.g. 1234567.')); return; }
  if (id !== S.id) { S.ft = null; S.loaded = {}; }
  S.id = id; localStorage.setItem('fpl_id', id);
  busy($('#team-out'), 'Reading your team and working out the best moves...');
  try { S.team = await api('/api/team', {id: id, h: horizon(), ft: S.ft}, fresh); renderTeam(S.team); }
  catch (e) { fail($('#team-out'), e); }
}

/* ---------- Chips ---------- */
const VERDICT = {play_now: ['Play now', 'ok'], use_soon: ['Use soon', 'warn'], consider: ['Consider', 'warn'], hold: ['Hold', ''], good: ['Good week found', 'ok'], wait: ['Wait', ''],
  available: ['Available', 'ok'], used: ['Used', ''], locked: ['Not open yet', ''], expired: ['Expired', 'bad']};
function chipCard(c) {
  const v = VERDICT[c.verdict] || [c.verdict, ''];
  let h = '<div class="chipc"><h3>' + esc(c.label) + ' <span class="tag ' + v[1] + '">' + v[0] + '</span></h3><div class="small muted">GW' + c.start + '&ndash;' + c.stop + '</div><p style="margin:6px 0">' + esc(c.headline) + '</p>';
  if (c.options && c.options.length) {
    const unit = c.name === 'bboost' ? 'bench pts' : c.name === '3xc' ? 'extra pts' : 'pts gain';
    h += c.options.map(o => '<div class="opt' + (o.best ? ' star' : '') + '">' + (o.best ? '&#9733; ' : '') + 'GW' + o.gw + ': <b>' + o.gain.toFixed(1) + '</b> ' + unit + '<div class="muted">' + esc(o.note) + '</div></div>').join('');
  }
  return h + '</div>';
}
function renderChips(d) {
  const first = d.chips.filter(c => c.start <= d.gw_next && c.stop >= d.gw_next);
  const later = d.chips.filter(c => c.start > d.gw_next);
  let h = '<div class="card"><h2>Your chips</h2><p class="small muted" style="margin-top:0">Only one chip can be played per gameweek. The first set must be used before the GW19 deadline. Advice is based on your current squad (' + d.unavailable + ' player(s) unavailable) and ' + d.ft + ' free transfer(s).</p><div class="chips4">' + first.map(chipCard).join('') + '</div></div>';
  if (later.length) h += '<div class="card"><h2>Second half of the season</h2><div class="chips4">' + later.map(chipCard).join('') + '</div></div>';
  if (d.specials.length) h += '<div class="card"><h2>Blank &amp; double gameweeks in the fixture list</h2>' + d.specials.map(s => '<span class="tag ' + (s.blank >= s.double ? 'bad' : 'ok') + '" style="margin:2px">GW' + s.gw + ': ' + (s.blank ? s.blank + ' teams blank' : '') + (s.blank && s.double ? ', ' : '') + (s.double ? s.double + ' teams double' : '') + '</span>').join('') + '<p class="small muted">Dates can still change as fixtures are rearranged. Check back as they are confirmed.</p></div>';
  h += '<div class="card"><h2>Gameweek by gameweek (your current squad)</h2><div class="scroll"><table><tr><th>GW</th><th>Games</th><th class="n">Your XI</th><th class="n">Bench</th><th>Best captain</th><th class="n">Players with a game</th><th class="n">Free Hit gain</th><th class="n">Bench Boost potential</th></tr>' +
    d.table.map(r => '<tr class="' + (r.double ? 'sp-d' : r.blank ? 'sp-b' : '') + '"><td><b>' + r.gw + '</b> <span class="muted small">' + fmtDate(r.deadline) + '</span></td><td>' + r.fixtures + (r.blank ? ' <span class="tag bad">' + r.blank + ' blank</span>' : '') + (r.double ? ' <span class="tag ok">' + r.double + ' double</span>' : '') + '</td><td class="n">' + r.xi.toFixed(1) + '</td><td class="n">' + r.bench.toFixed(1) + '</td><td>' + esc(r.cap_name) + ' (' + r.cap.toFixed(1) + ')</td><td class="n">' + r.playing + '/15</td><td class="n">' + (r.fh == null ? '&ndash;' : r.fh.toFixed(1)) + '</td><td class="n">' + (r.bb == null ? '&ndash;' : r.bb.toFixed(1)) + '</td></tr>').join('') +
    '</table></div><p class="small muted">Free Hit gain and Bench Boost potential are only worked out for the most interesting gameweeks (the next two, plus blanks and doubles).</p></div>';
  const out = $('#chips-out'); out.className = ''; out.innerHTML = h;
}
async function loadChips(fresh) {
  const id = $('#tid').value.trim();
  if (!/^\d+$/.test(id)) { $('#chips-out').className = 'empty'; $('#chips-out').textContent = 'Enter your team ID above first.'; return; }
  S.id = id; localStorage.setItem('fpl_id', id);
  busy($('#chips-out'), 'Working out the best week for each chip (this takes a few seconds)...');
  try { renderChips(await api('/api/chips', {id: id}, fresh)); S.loaded.chips = id; }
  catch (e) { fail($('#chips-out'), e); }
}

/* ---------- Build a team ---------- */
async function buildTeam() {
  const out = $('#build-out');
  busy(out, 'Searching thousands of squads...');
  try {
    const d = await api('/api/build', {budget: $('#budget').value, h: horizon()});
    out.innerHTML = '<div class="card"><h2>Best squad for ' + money(d.budget) + ' over the next ' + d.horizon + ' gameweek' + (d.horizon > 1 ? 's' : '') + '</h2><div class="grid">' + stat('Squad cost', money(d.cost)) + stat('Left in the bank', money(d.bank)) +
      stat('Projected points (XI + captain)', d.xp_total.toFixed(0)) + stat('Formation', esc(d.formation)) + '</div></div><div class="card">' + pitch(d) + '</div>' +
      '<div class="card"><h2>Full list</h2><div class="scroll"><table><tr><th>Pos</th><th>Player</th><th>Club</th><th class="n">Price</th><th class="n">Next GW</th><th class="n">Next ' + d.horizon + '</th><th>Fixtures</th></tr>' +
      d.squad.map(c => '<tr><td>' + POS[c.pos] + '</td><td><b>' + esc(c.name) + '</b>' + (c.id === d.captain ? ' (C)' : c.id === d.vice ? ' (V)' : '') + '</td><td>' + esc(c.team) + '</td><td class="n">' + money(c.price) + '</td><td class="n">' + c.xp1.toFixed(1) + '</td><td class="n">' + c.xph.toFixed(1) + '</td><td>' + fxCells(c.fx, 5) + '</td></tr>').join('') + '</table></div></div>';
  } catch (e) { fail(out, e); }
}

/* ---------- Players & prices ---------- */
async function loadPlayers(fresh) {
  const out = $('#pl-table'); busy(out, 'Loading every player...');
  try {
    S.players = await api('/api/players', {h: horizon()}, fresh);
    const sel = $('#fteam');
    if (sel.options.length <= 1) S.players.teams.forEach(t => { const o = document.createElement('option'); o.value = t; o.textContent = t; sel.appendChild(o); });
    drawPlayers(); drawWatch();
  } catch (e) { fail(out, e); }
}
let plLimit = 60;
function meter(pc) {
  if (pc == null) return '';
  const w = Math.min(50, Math.abs(pc) / 2);
  return '<span class="meter" title="' + pc.toFixed(0) + '% of the way to a price change"><i class="' + (pc >= 0 ? 'p' : 'm') + '" style="width:' + w + '%"></i></span> <span class="small muted">' + (pc >= 0 ? '+' : '') + pc.toFixed(0) + '%</span>';
}
function drawPlayers() {
  if (!S.players) return;
  const q = $('#q').value.trim().toLowerCase(), pos = +$('#fpos').value, tm = $('#fteam').value, mx = Math.round(parseFloat($('#fmax').value || '99') * 10), av = $('#favail').checked, key = $('#fsort').value;
  const meterOf = p => p.pj[0] != null ? p.pj[0] : (p.pc || 0);
  const L = S.players.players.filter(p => (!q || p.n.toLowerCase().indexOf(q) >= 0) && (!pos || p.p === pos) && (!tm || p.t === tm) && p.c <= mx && (!av || p.ok));
  L.sort((a, b) => key === 'pj' ? meterOf(b) - meterOf(a) : (b[key] - a[key]));
  const shown = L.slice(0, plLimit);
  $('#pl-table').innerHTML = '<div class="small muted" style="margin-bottom:6px">' + L.length + ' players match. Prices are live from FPL.</div><div class="scroll"><table><tr><th>Player</th><th>Pos</th><th class="n">Price</th><th class="n">Since start</th><th class="n">Own %</th><th class="n">Form</th><th class="n">Next GW</th><th class="n">Next ' + S.players.gws.length + '</th><th>Fixtures</th><th>Price meter</th><th>News</th></tr>' +
    shown.map(p => {
      const d = p.cs ? (p.cs > 0 ? '+' : '') + (p.cs / 10).toFixed(1) : '0.0';
      return '<tr><td><b>' + esc(p.n) + '</b> <span class="muted small">' + esc(p.t) + '</span></td><td>' + POS[p.p] + '</td><td class="n">' + money(p.c) + '</td><td class="n" style="color:' + (p.cs > 0 ? 'var(--ok)' : p.cs < 0 ? 'var(--bad)' : 'inherit') + '">' + d + '</td><td class="n">' + p.o.toFixed(1) + '</td><td class="n">' + p.f.toFixed(1) + '</td><td class="n"><b>' + p.x1.toFixed(1) + '</b></td><td class="n">' + p.xh.toFixed(1) + '</td><td>' + fxCells(p.fx, 3) + '</td><td>' + meter(p.pj[0] != null ? p.pj[0] : p.pc) + '</td><td class="small muted">' + esc(p.nw) + '</td></tr>';
    }).join('') + '</table></div>' + (L.length > plLimit ? '<p><button id="more">Show 60 more</button></p>' : '');
  const more = $('#more'); if (more) more.onclick = () => { plLimit += 60; drawPlayers(); };
}
function drawWatch() {
  const P = S.players.players.filter(p => p.ok && p.o >= 0.5 && p.pj.length);
  const ris = P.filter(p => p.pj[0] > 0).sort((a, b) => b.pj[0] - a.pj[0]).slice(0, 10);
  const fal = P.filter(p => p.pj[0] < 0).sort((a, b) => a.pj[0] - b.pj[0]).slice(0, 10);
  const list = (arr, up) => arr.map(p => '<tr><td><b>' + esc(p.n) + '</b> <span class="muted small">' + esc(p.t) + ' ' + POS[p.p] + '</span></td><td class="n">' + money(p.c) + '</td><td>' + meter(p.pj[0]) + '</td><td class="small muted">' + (Math.abs(p.pj[0]) >= 100 ? '<b style="color:var(--' + (up ? 'ok' : 'bad') + ')">' + (up ? 'rise' : 'fall') + ' due</b>' : 'owned by ' + p.o.toFixed(1) + '%') + '</td></tr>').join('');
  $('#pw').innerHTML = '<div class="card"><h2>Closest to a price rise</h2><table>' + list(ris, true) + '</table></div><div class="card"><h2>Closest to a price fall</h2><table>' + list(fal, false) + '</table></div>' +
    '<p class="small muted" style="grid-column:1/-1">The meter comes from the official FPL feed: at +100% a player rises at the next price change, at -100% he falls. Prices change overnight.</p>';
}

/* ---------- Fixtures ---------- */
async function loadFixtures(fresh) {
  const out = $('#fx-out'); busy(out, 'Loading fixtures...');
  try {
    const d = await api('/api/fixtures', {n: 8}, fresh);
    out.innerHTML = '<div class="card"><h2>Fixture difficulty</h2><p class="small muted" style="margin-top:0">Red columns are blank gameweeks (some teams have no match), green columns are doubles.</p><div class="scroll"><table class="grid-fx"><tr><th>Club</th>' +
      d.gws.map(g => '<th class="' + (d.info[g].blank ? 'sp-b' : d.info[g].double ? 'sp-d' : '') + '">GW' + g + (d.info[g].blank ? '<br><small>' + d.info[g].blank + ' blank</small>' : '') + (d.info[g].double ? '<br><small>' + d.info[g].double + ' double</small>' : '') + '</th>').join('') + '<th>Avg next 5</th></tr>' +
      d.teams.map(t => '<tr><td><b>' + esc(t.short) + '</b> <span class="muted small">' + esc(t.name) + '</span></td>' + t.rows.map(r => '<td>' + (r.length ? r.map(fxTag).join(' ') : '<span class="fx f0">-</span>') + '</td>').join('') + '<td>' + (t.avg == null ? '-' : t.avg.toFixed(1)) + '</td></tr>').join('') + '</table></div></div>';
  } catch (e) { fail(out, e); }
}

/* ---------- wiring ---------- */
function showTab(name) {
  document.querySelectorAll('#tabs button').forEach(b => b.classList.toggle('on', b.dataset.tab === name));
  document.querySelectorAll('main > section').forEach(s => s.classList.toggle('on', s.id === 'tab-' + name));
  const id = $('#tid').value.trim();
  if (name === 'chips' && S.loaded.chips !== id && /^\d+$/.test(id)) loadChips();
  if (name === 'players' && !S.players) loadPlayers();
  if (name === 'fixtures' && !S.loaded.fixtures) { S.loaded.fixtures = 1; loadFixtures(); }
}
$('#tabs').addEventListener('click', e => { const b = e.target.closest('button[data-tab]'); if (b) showTab(b.dataset.tab); });
$('#load').addEventListener('click', () => {
  const on = document.querySelector('#tabs button.on').dataset.tab;
  if (on === 'chips') loadChips(); else { if (on !== 'team') showTab('team'); loadTeam(); }
});
$('#tid').addEventListener('keydown', e => { if (e.key === 'Enter') $('#load').click(); });
$('#hor').addEventListener('change', () => { S.players = null; if (S.team) loadTeam(); if ($('#tab-players').classList.contains('on')) loadPlayers(); });
$('#refresh').addEventListener('click', async () => {
  const b = $('#refresh'); b.disabled = true; b.textContent = 'Refreshing...';
  await loadStatus(true); S.players = null; S.loaded = {};
  const on = document.querySelector('#tabs button.on').dataset.tab;
  if (on === 'team' && S.id) loadTeam(true); else if (on === 'players') loadPlayers(); else if (on === 'chips') loadChips(true); else if (on === 'fixtures') { S.loaded.fixtures = 1; loadFixtures(); }
  b.disabled = false; b.textContent = 'Refresh data';
});
$('#build').addEventListener('click', buildTeam);
$('#usemine').addEventListener('click', () => {
  if (!S.team) { alert('Load your team first (enter your team ID and press Load my team).'); return; }
  $('#budget').value = ((S.team.value + S.team.bank) / 10).toFixed(1);
});
['q', 'fpos', 'fteam', 'fmax', 'favail', 'fsort'].forEach(id => $('#' + id).addEventListener('input', () => { plLimit = 60; drawPlayers(); }));
$('#tid').value = S.id;
loadStatus();
if (S.id) loadTeam();
</script>
</body>
</html>
'''


class FPLError(Exception):
    """Something the user should be told about in plain English."""


class NotFound(FPLError):
    pass


class UserError(FPLError):
    """The request itself was wrong (e.g. no team ID typed in)."""


def num(x, default=0.0):
    try:
        if x is None or x == "":
            return default
        return float(x)
    except (TypeError, ValueError):
        return default


def clamp(x, lo, hi):
    return lo if x < lo else hi if x > hi else x


def parse_time(s):
    if not s:
        return None
    try:
        s = s.replace("Z", "+00:00")
        s = re.sub(r"(\.\d{6})\d+", r"\1", s)
        d = datetime.fromisoformat(s)
        return d if d.tzinfo else d.replace(tzinfo=timezone.utc)
    except ValueError:
        return None


def selling_price(now_cost, buy_cost):
    """FPL sells at purchase price + half of any profit (rounded down to 0.1m)."""
    if now_cost > buy_cost:
        return buy_cost + (now_cost - buy_cost) // 2
    return now_cost


class Source(object):
    """Downloads JSON from the FPL API and keeps a short-lived cache."""

    def __init__(self, fetcher=None):
        self._fetcher = fetcher
        self._cache = {}
        self._lock = threading.Lock()
        self._dl_lock = threading.Lock()

    def get(self, path, ttl=120, force=False):
        now = time.time()
        with self._lock:
            hit = self._cache.get(path)
        if hit and not force and now - hit[0] < ttl:
            return hit[1]
        with self._dl_lock:                      # one download at a time; reuse one that just finished
            with self._lock:
                hit = self._cache.get(path)
            if hit and ((not force and now - hit[0] < ttl) or time.time() - hit[0] < 3):
                return hit[1]
            data = self._fetcher(path) if self._fetcher else self._download(path)
            with self._lock:
                self._cache[path] = (time.time(), data)
            return data

    def stamp(self, path):
        hit = self._cache.get(path)
        return hit[0] if hit else None

    @staticmethod
    def _download(path):
        req = Request(API_ROOT + path, headers={"User-Agent": USER_AGENT, "Accept": "application/json",
                                                "Accept-Encoding": "gzip"})
        problem = "Couldn't download data from FPL."
        for attempt in range(3):
            try:
                with urlopen(req, timeout=30) as resp:
                    body = resp.read()
                    if (resp.headers.get("Content-Encoding") or "").lower() == "gzip":
                        body = gzip.decompress(body)
                    raw = body.decode("utf-8", "replace")
                try:
                    return json.loads(raw)
                except ValueError:
                    if "updated" in raw.lower():
                        problem = "FPL is being updated right now (this usually takes 5-30 minutes). Try again shortly."
                    else:
                        problem = "FPL sent back something unreadable."
            except HTTPError as e:
                if e.code == 404:
                    raise NotFound("FPL says that page doesn't exist (%s). Check the team ID." % path)
                if e.code == 429:
                    problem = "FPL is rate-limiting requests. Wait a minute and try again."
                elif e.code in (500, 502, 503, 504):
                    problem = "FPL's servers are busy or updating (error %d). This usually clears in a few minutes." % e.code
                else:
                    problem = "FPL refused the request (HTTP %d)." % e.code
            except URLError as e:
                reason = getattr(e, "reason", e)
                if isinstance(reason, ssl.SSLError) or "CERTIFICATE" in str(reason).upper():
                    raise FPLError("Secure connection failed (%s). On a Mac, run 'Install Certificates.command' "
                                   "from your Python folder, then try again." % reason)
                problem = ("Can't reach fantasy.premierleague.com (%s). Check your internet connection - "
                           "some school/college networks block it." % reason)
            except OSError as e:
                problem = "Network problem talking to FPL (%s)." % e
            time.sleep(1.0 * (attempt + 1))
        raise FPLError(problem)


# ----------------------------------------------------------------------------
# The projection model
# ----------------------------------------------------------------------------

def prior_pp90(pos, price_m):
    """A rough 'points per 90' guess for a regular starter at this price."""
    if pos == 1:
        v = 3.4 + 0.28 * (price_m - 4.0)
    elif pos == 2:
        v = 3.0 + 0.45 * (price_m - 4.0)
    elif pos == 3:
        v = 2.6 + 0.62 * (price_m - 4.5)
    else:
        v = 2.8 + 0.55 * (price_m - 4.5)
    return max(1.5, v)


def pos_mult(pos, att, cs):
    if pos == 1:
        return 0.15 * att + 0.85 * cs
    if pos == 2:
        return 0.30 * att + 0.70 * cs
    if pos == 3:
        return 0.85 * att + 0.15 * cs
    return att


class Model(object):
    """Turns raw FPL data into projected points for every player and gameweek."""

    def __init__(self, bs, fixtures, now=None):
        self.now = now or datetime.now(timezone.utc)
        gs = bs.get("game_settings") or {}
        self.budget = int(gs.get("squad_total_spend") or 1000)
        self.team_limit = int(gs.get("squad_team_limit") or 3)
        self.ft_cap = 1 + int(gs.get("max_extra_free_transfers") or 4)
        self.total_managers = int(bs.get("total_players") or 1)
        cfg = bs.get("game_config") or {}
        self.price_deadlines = list((cfg.get("settings") or {}).get("price_change_deadlines") or [])
        self.price_updated = (cfg.get("status") or {}).get("price_change_last_updated")
        self.chips = bs.get("chips") or []
        self.teams = {t["id"]: t for t in bs["teams"]}
        self.events = {e["id"]: e for e in bs["events"]}
        self.players = {p["id"]: p for p in bs["elements"] if p.get("element_type") in POS_NAMES}
        evs = bs["events"]
        self.current = next((e["id"] for e in evs if e.get("is_current")), None)
        self.next = next((e["id"] for e in evs if e.get("is_next")), None)
        if self.next is None:
            raise FPLError("FPL has no upcoming gameweek open right now (the season is over, or the game is "
                           "between seasons). Try again closer to the next gameweek.")
        self.first = self.next
        self.last_gw = max(self.events)
        self.gws_played = sum(1 for e in evs if e.get("finished"))
        self.deadline = parse_time(self.events[self.next].get("deadline_time"))
        top = max(self.players) + 1
        self.pos_of = [0] * top
        self.team_of = [0] * top
        self.price = [0] * top
        self.by_pos = {1: [], 2: [], 3: [], 4: []}
        self.eligible = [False] * top
        for pid, p in self.players.items():
            self.pos_of[pid] = p["element_type"]
            self.team_of[pid] = p["team"]
            self.price[pid] = int(p["now_cost"])
            self.by_pos[p["element_type"]].append(pid)
            ok = (p.get("status", "a") in ("a", "d") and p.get("can_select", True) is not False
                  and not p.get("removed"))
            self.eligible[pid] = bool(ok)
        self._index_fixtures(fixtures)
        self._team_strength()
        self._project()

    # -- fixtures -----------------------------------------------------------
    def _index_fixtures(self, fixtures):
        self.fx = defaultdict(list)
        for f in fixtures:
            gw = f.get("event")
            if not gw or gw < self.first:
                continue
            h, a = f.get("team_h"), f.get("team_a")
            if h not in self.teams or a not in self.teams:
                continue
            self.fx[(h, gw)].append((a, True, int(f.get("team_h_difficulty") or 3)))
            self.fx[(a, gw)].append((h, False, int(f.get("team_a_difficulty") or 3)))
        self.gw_info = {}
        for gw in range(self.first, self.last_gw + 1):
            blank = [t for t in self.teams if not self.fx.get((t, gw))]
            double = [t for t in self.teams if len(self.fx.get((t, gw), [])) >= 2]
            n = sum(len(self.fx.get((t, gw), [])) for t in self.teams) // 2
            self.gw_info[gw] = {"fixtures": n, "blank": blank, "double": double}

    def _team_strength(self):
        """Attack/defence quality of each club from this season's xG data (shrunk towards average)."""
        games, xg, xga = defaultdict(float), defaultdict(float), defaultdict(float)
        for p in self.players.values():
            t = p["team"]
            xg[t] += num(p.get("expected_goals"))
            if p["element_type"] == 1:
                games[t] += num(p.get("minutes")) / 90.0
                xga[t] += num(p.get("expected_goals_conceded"))
        tot = sum(games.values())
        self.team_rel = {}
        self.avg_xg = 1.35
        if tot < 10:
            return
        avg_for = sum(xg.values()) / tot
        avg_against = sum(xga.values()) / tot
        if avg_for <= 0 or avg_against <= 0:
            return
        self.avg_xg = (avg_for + avg_against) / 2.0
        k = 4.0
        for t in self.teams:
            g = games.get(t, 0.0)
            self.team_rel[t] = {"att": ((xg.get(t, 0.0) + k * avg_for) / (g + k)) / avg_for,
                                "def": ((xga.get(t, 0.0) + k * avg_against) / (g + k)) / avg_against}

    def _fixture_terms(self, tid, oid, home, fdr):
        f = FDR_MULT.get(int(fdr), 1.0)
        att = cs = f
        a, b = self.team_rel.get(tid), self.team_rel.get(oid)
        if a and b:
            att_x = clamp(b["def"] * (1.10 if home else 0.92), 0.6, 1.6)
            xgc = self.avg_xg * a["def"] * b["att"] * (0.90 if home else 1.12)
            cs_x = clamp(math.exp(self.avg_xg - xgc), 0.4, 1.9)
            att = 0.6 * f + 0.4 * att_x
            cs = 0.6 * f + 0.4 * cs_x
        return att, cs

    # -- availability -------------------------------------------------------
    def _return_date(self, p):
        m = re.search(r"(\d{1,2})\s+(Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)", p.get("news") or "", re.I)
        if not m:
            return None
        try:
            d = datetime(self.now.year, MONTHS[m.group(2).lower()[:3]], int(m.group(1)), tzinfo=timezone.utc)
        except ValueError:
            return None
        if d < self.now - timedelta(days=60):
            d = d.replace(year=d.year + 1)
        return d

    def _avail(self, p, gw):
        status = p.get("status", "a")
        if status in ("u", "n"):
            return 0.0
        chance = p.get("chance_of_playing_next_round")
        if status == "a" and chance is None:
            return 1.0
        base = 1.0 if chance is None else clamp(chance / 100.0, 0.0, 1.0)
        k = gw - self.first
        if k <= 0:
            return base
        if status == "d":
            return min(1.0, base + 0.2 * k)
        ret = self._return_date(p)
        dl = parse_time((self.events.get(gw) or {}).get("deadline_time"))
        if ret and dl:
            if ret <= dl:
                return 0.9
            if ret <= dl + timedelta(days=3):
                return 0.5
            return 0.0
        if status in ("i", "s"):
            return min(0.8, 0.25 * k)
        return base

    # -- per-player rates ---------------------------------------------------
    def _rate(self, p):
        pos = p["element_type"]
        mins = num(p.get("minutes"))
        prior = prior_pp90(pos, p["now_cost"] / 10.0)
        pp90 = num(p.get("total_points")) / mins * 90.0 if mins > 0 else 0.0
        if mins >= 180:
            xg, xa = num(p.get("expected_goals")), num(p.get("expected_assists"))
            if xg or xa:
                luck = (num(p.get("goals_scored")) - xg) * GOAL_PTS[pos] + (num(p.get("assists")) - xa) * 3.0
                pp90 -= 0.5 * clamp(luck / mins * 90.0, -3.0, 3.0) * min(1.0, mins / 900.0)
        w = mins / (mins + PRIOR_MINUTES)
        rate = w * pp90 + (1.0 - w) * prior
        fw = 0.22 * min(1.0, mins / 450.0)
        rate = (1.0 - fw) * rate + fw * num(p.get("form"))
        return max(rate, 0.0)

    def _minutes_frac(self, p):
        games = self.gws_played
        if games <= 0:
            return 0.8
        mins = num(p.get("minutes"))
        share = (mins + 2 * 90 * 0.6) / ((games + 2) * 90.0)
        return clamp(share * 1.05, 0.03, 0.95)

    def _project(self):
        self.xp = {}
        self.rate = {}
        for pid, p in self.players.items():
            pos = p["element_type"]
            rate = self._rate(p)
            mf = self._minutes_frac(p)
            self.rate[pid] = rate
            v = VAR_SHARE[pos]
            xs = {}
            for gw in range(self.first, self.last_gw + 1):
                fx = self.fx.get((p["team"], gw))
                tot = 0.0
                if fx:
                    av = self._avail(p, gw)
                    if av > 0:
                        for (opp, home, fdr) in fx:
                            att, cs = self._fixture_terms(p["team"], opp, home, fdr)
                            tot += rate * mf * av * ((1.0 - v) + v * pos_mult(pos, att, cs))
                xs[gw] = tot
            self.xp[pid] = xs

    # -- helpers used by the rest of the app ---------------------------------
    def gws(self, horizon):
        return list(range(self.first, min(self.last_gw, self.first + max(1, horizon) - 1) + 1))

    def vals(self, gws):
        """List indexed by player id: total projected points over these gameweeks."""
        out = [0.0] * len(self.pos_of)
        for pid, xs in self.xp.items():
            out[pid] = sum(xs.get(g, 0.0) for g in gws)
        return out

    def fixture_list(self, tid, gws):
        res = []
        for g in gws:
            res.append([{"o": self.teams[o]["short_name"], "h": h, "d": d} for (o, h, d) in self.fx.get((tid, g), [])])
        return res

    def avg_fdr(self, tid, gws):
        ds = [d for g in gws for (_, _, d) in self.fx.get((tid, g), [])]
        return sum(ds) / len(ds) if ds else None

    def n_fixtures(self, tid, gws):
        return sum(len(self.fx.get((tid, g), [])) for g in gws)

    def card(self, pid, val, gws, sell=None, buy=None):
        p = self.players[pid]
        t = self.teams[p["team"]]
        return {
            "id": pid, "name": p.get("web_name") or p.get("second_name"), "team": t["short_name"],
            "pos": p["element_type"], "price": int(p["now_cost"]), "sell": sell, "buy": buy,
            "xp1": round(self.xp[pid].get(self.first, 0.0), 1), "xph": round(val[pid], 1),
            "form": num(p.get("form")), "status": p.get("status", "a"), "news": p.get("news") or "",
            "chance": p.get("chance_of_playing_next_round"),
            "fx": self.fixture_list(p["team"], gws[:5]), "sel": num(p.get("selected_by_percent")),
            "pc": num(p.get("price_change_percent"), None), "pj": self.price_proj(p),
        }

    @staticmethod
    def price_proj(p):
        """Official price-change meter: projected % progress at the next three price changes (+-100 = change)."""
        out = []
        for x in (p.get("price_change_projections") or [])[:3]:
            out.append(num(x.get("projected_percent")))
        return out


# ----------------------------------------------------------------------------
# Squad maths: scoring a squad, picking the XI, building and improving squads
# ----------------------------------------------------------------------------

def squad_score(ids, val, pos_of, bench_w):
    """Value of a 15-man squad (2 GK, 5 DEF, 5 MID, 3 FWD): best XI + captain bonus + a little for the bench."""
    g, d, m, f = [], [], [], []
    for i in ids:
        p = pos_of[i]
        if p == 2:
            d.append(val[i])
        elif p == 3:
            m.append(val[i])
        elif p == 4:
            f.append(val[i])
        else:
            g.append(val[i])
    g.sort(reverse=True)
    d.sort(reverse=True)
    m.sort(reverse=True)
    f.sort(reverse=True)
    rest = d[3:] + m[2:] + f[1:]
    rest.sort(reverse=True)
    xi = g[0] + d[0] + d[1] + d[2] + m[0] + m[1] + f[0] + rest[0] + rest[1] + rest[2] + rest[3]
    bench = g[1] + rest[4] + rest[5] + rest[6]
    return xi + max(g[0], d[0], m[0], f[0]) + bench_w * bench


def pick_xi(ids, val, pos_of, cap_val=None):
    """Best starting XI, bench order, formation, captain and vice-captain for a squad."""
    by = {1: [], 2: [], 3: [], 4: []}
    for i in ids:
        by[pos_of[i]].append(i)
    for p in by:
        by[p].sort(key=lambda i: -val[i])
    xi = {1: by[1][:1], 2: by[2][:3], 3: by[3][:2], 4: by[4][:1]}
    rest = by[2][3:] + by[3][2:] + by[4][1:]
    rest.sort(key=lambda i: -val[i])
    for i in rest[:4]:
        xi[pos_of[i]].append(i)
    for p in xi:
        xi[p].sort(key=lambda i: -val[i])
    starters = xi[1] + xi[2] + xi[3] + xi[4]
    bench = by[1][1:] + rest[4:]
    cv = cap_val if cap_val is not None else val
    ranked = sorted(starters, key=lambda i: -cv[i])
    return {"xi": starters, "bench": bench, "captain": ranked[0], "vice": ranked[1],
            "formation": "%d-%d-%d" % (len(xi[2]), len(xi[3]), len(xi[4]))}


def make_pools(m, val, per_pos=55, cheap=14, extra=14, exclude=()):
    """Candidate players per position: the best by points, the cheapest, and the best value for money."""
    pools = {}
    for pos in (1, 2, 3, 4):
        elig = [i for i in m.by_pos[pos] if m.eligible[i] and i not in exclude]
        top = sorted(elig, key=lambda i: -val[i])[:per_pos]
        cheapest = sorted(elig, key=lambda i: (m.price[i], -val[i]))[:cheap]
        value = sorted(elig, key=lambda i: -(val[i] / max(m.price[i], 35.0)))[:extra]
        pools[pos] = list(dict.fromkeys(top + cheapest + value))
    return pools


def _initial_squad(m, pools, budget, rng, randomise):
    need = [1] * 2 + [2] * 5 + [3] * 5 + [4] * 3
    min_price = {p: min(m.price[i] for i in pools[p]) for p in pools}
    ids, cost, cnt = [], 0, Counter()
    for idx, p in enumerate(need):
        rest_min = sum(min_price[q] for q in need[idx + 1:])
        cands = [i for i in pools[p] if i not in ids and cnt[m.team_of[i]] < m.team_limit
                 and cost + m.price[i] + rest_min <= budget]
        if not cands:
            return None
        cands.sort(key=lambda i: m.price[i])
        pick = rng.choice(cands[:12]) if randomise else cands[0]
        ids.append(pick)
        cost += m.price[pick]
        cnt[m.team_of[pick]] += 1
    return ids


def optimise_squad(m, val, budget, pools, iters=40000, restarts=3, seed=11, bench_w=BENCH_WEIGHT):
    """Search for the highest-scoring legal squad. Returns (score, ids) or (None, None)."""
    iters = max(4000, int(iters * EFFORT))
    rng = random.Random(seed)
    pos_of, team_of, price, limit = m.pos_of, m.team_of, m.price, m.team_limit
    best_score, best_ids = None, None
    top = max([val[i] for p in pools for i in pools[p]] + [1.0])
    for r in range(restarts):
        ids = _initial_squad(m, pools, budget, rng, randomise=(r > 0))
        if ids is None:
            continue
        inset = set(ids)
        cost = sum(price[i] for i in ids)
        cnt = Counter(team_of[i] for i in ids)
        score = squad_score(ids, val, pos_of, bench_w)
        t0 = 0.05 * top + 0.01
        for it in range(iters):
            temp = t0 * (1.0 - it / float(iters)) + 1e-3
            if rng.random() < 0.35:
                slots = rng.sample(range(15), 2)       # a double swap: lets money move between two slots
            else:
                slots = [rng.randrange(15)]
            olds = [ids[s] for s in slots]
            news = []
            ncost = cost
            ok = True
            for s, old in zip(slots, olds):
                cand = rng.choice(pools[pos_of[old]])
                if cand in inset or cand in news:
                    ok = False
                    break
                news.append(cand)
                ncost += price[cand] - price[old]
            if not ok or ncost > budget:
                continue
            c2 = Counter(cnt)
            for old, cand in zip(olds, news):
                c2[team_of[old]] -= 1
                c2[team_of[cand]] += 1
            if any(c2[team_of[cand]] > limit for cand in news):
                continue
            for s, cand in zip(slots, news):
                ids[s] = cand
            ns = squad_score(ids, val, pos_of, bench_w)
            d = ns - score
            if d >= 0 or rng.random() < math.exp(d / temp):
                for old in olds:
                    inset.discard(old)
                inset.update(news)
                cnt, cost, score = c2, ncost, ns
            else:
                for s, old in zip(slots, olds):
                    ids[s] = old
        # polish: keep taking the single best improving swap until none is left
        improved = True
        while improved:
            improved = False
            best_move = None
            for s in range(15):
                old = ids[s]
                for cand in pools[pos_of[old]]:
                    if cand in inset or cost - price[old] + price[cand] > budget:
                        continue
                    tc, to = team_of[cand], team_of[old]
                    if tc != to and cnt[tc] >= limit:
                        continue
                    ids[s] = cand
                    ns = squad_score(ids, val, pos_of, bench_w)
                    ids[s] = old
                    if ns > score + 1e-9 and (best_move is None or ns > best_move[0]):
                        best_move = (ns, s, cand)
            if best_move:
                ns, s, cand = best_move
                old = ids[s]
                inset.discard(old)
                inset.add(cand)
                cnt[team_of[old]] -= 1
                cnt[team_of[cand]] += 1
                cost += price[cand] - price[old]
                ids[s] = cand
                score = ns
                improved = True
        if best_score is None or score > best_score:
            best_score, best_ids = score, list(ids)
    return best_score, best_ids


def plan_transfers(m, squad, bank, sell, val, pools, max_k=3, beam=25, bench_w=BENCH_WEIGHT):
    """Beam search over 1..max_k transfers. Returns (base_score, {k: (score, ids, bank, moves)})."""
    pos_of, team_of, price, limit = m.pos_of, m.team_of, m.price, m.team_limit
    base = squad_score(squad, val, pos_of, bench_w)
    start = (base, tuple(squad), bank, ())
    frontier = [start]
    best = {0: start}
    for k in range(1, max_k + 1):
        nxt = {}
        for (score, ids, b, moves) in frontier:
            have = set(ids)
            bought = set(mv[1] for mv in moves)
            sold = set(mv[0] for mv in moves)
            cnt = Counter(team_of[i] for i in ids)
            for idx, out in enumerate(ids):
                if out in bought:
                    continue
                room = b + sell[out]
                to = team_of[out]
                for cand in pools[pos_of[out]]:
                    if cand in have or cand in sold or price[cand] > room:
                        continue
                    tc = team_of[cand]
                    if tc != to and cnt[tc] >= limit:
                        continue
                    new = ids[:idx] + (cand,) + ids[idx + 1:]
                    key = frozenset(new)
                    if key in nxt:
                        continue
                    nxt[key] = (squad_score(new, val, pos_of, bench_w), new, room - price[cand],
                                moves + ((out, cand),))
        if not nxt:
            break
        frontier = sorted(nxt.values(), key=lambda s: -s[0])[:beam]
        best[k] = frontier[0]
    return base, best


# ----------------------------------------------------------------------------
# Your team: import from FPL, transfer advice, captaincy, chips
# ----------------------------------------------------------------------------

def load_squad(src, m, entry_id, fresh=False):
    """Read a manager's squad, bank and selling prices from FPL's public endpoints."""
    if m.current is None:
        raise FPLError("Gameweek 1 hasn't been played yet, so there's no locked-in squad to analyse. "
                       "Use the Build a Team tab instead.")
    entry = src.get("entry/%d/" % entry_id, ttl=60, force=fresh)
    hist = src.get("entry/%d/history/" % entry_id, ttl=60, force=fresh)
    transfers = src.get("entry/%d/transfers/" % entry_id, ttl=60, force=fresh)
    fh_events = set(c.get("event") for c in (hist.get("chips") or []) if c.get("name") == "freehit")
    base, picks = m.current, None
    while base >= 1:
        try:
            p = src.get("entry/%d/event/%d/picks/" % (entry_id, base), ttl=60, force=fresh)
        except NotFound:
            base -= 1
            continue
        if p.get("active_chip") == "freehit" and base > 1:
            base -= 1          # a Free Hit team is temporary - your real squad is last week's
            continue
        picks = p
        break
    if not picks or len(picks.get("picks") or []) != 15:
        raise FPLError("Couldn't read a full 15-player squad for team ID %d." % entry_id)
    squad = [x["element"] for x in sorted(picks["picks"], key=lambda x: x["position"])]
    for pid in squad:
        if pid not in m.players:
            raise FPLError("Your squad has a player FPL no longer lists (id %d). Try again after the next update." % pid)
    bank = (picks.get("entry_history") or {}).get("bank")
    if bank is None:
        bank = entry.get("last_deadline_bank") or 0
    bank = int(bank)
    ordered = sorted([t for t in (transfers or []) if t.get("event") not in fh_events], key=lambda t: t.get("time") or "")
    bought, made_next = {}, 0
    for t in ordered:
        bought[t["element_in"]] = int(t["element_in_cost"])
        if t.get("event") == m.next:            # transfers you've already made for the upcoming gameweek
            made_next += 1
            if t["element_out"] in squad:
                squad[squad.index(t["element_out"])] = t["element_in"]
            bank += int(t.get("element_out_cost") or 0) - int(t.get("element_in_cost") or 0)
    sell, buy = {}, {}
    for pid in squad:
        p = m.players[pid]
        now = int(p["now_cost"])
        b = bought.get(pid)
        if b is None:
            b = now - int(p.get("cost_change_start") or 0)     # in your squad since the start: bought at the start price
        buy[pid] = int(b)
        sell[pid] = selling_price(now, int(b))
    return {"entry": entry, "hist": hist, "squad": squad, "bank": bank, "sell": sell, "buy": buy,
            "base_gw": base, "made_next": made_next, "ft_est": estimate_free_transfers(m, entry, hist, made_next)}


def estimate_free_transfers(m, entry, hist, made_next):
    """Best guess of free transfers left for the next deadline (FPL doesn't publish this)."""
    start = int(entry.get("started_event") or 1)
    rows = dict((r.get("event"), r) for r in (hist.get("current") or []))
    chips = dict((c.get("event"), c.get("name")) for c in (hist.get("chips") or []))
    ft = 1
    for gw in range(start + 1, m.next):
        n = int((rows.get(gw) or {}).get("event_transfers") or 0)
        if chips.get(gw) in ("wildcard", "freehit"):
            ft = min(m.ft_cap, ft + 1)               # chips keep your banked transfers
        else:
            ft = min(m.ft_cap, max(ft - n, 0) + 1)
    return max(0, ft - made_next)


def why_out(m, pid, gws):
    p = m.players[pid]
    res = []
    if p.get("status") in ("i", "s", "u", "n"):
        res.append(p.get("news") or "Unavailable")
    elif p.get("status") == "d":
        res.append(p.get("news") or "Doubtful")
    n = m.n_fixtures(p["team"], gws)
    if n == 0:
        res.append("No fixtures in the next %d gameweek(s)" % len(gws))
    else:
        d = m.avg_fdr(p["team"], gws)
        if d is not None and d >= 3.6:
            res.append("Tough fixtures (average difficulty %.1f)" % d)
    if num(p.get("form")) < 2.0 and num(p.get("minutes")) > 270:
        res.append("Poor form (%.1f)" % num(p.get("form")))
    return res or ["Lower projected points than the replacement"]


def why_in(m, pid, gws):
    p = m.players[pid]
    res = []
    if num(p.get("form")) >= 5.0:
        res.append("In form (%.1f)" % num(p.get("form")))
    d = m.avg_fdr(p["team"], gws)
    if d is not None and d <= 2.8:
        res.append("Good fixtures (average difficulty %.1f)" % d)
    if m.n_fixtures(p["team"], gws) > len(gws):
        res.append("Double gameweek coming up")
    pc = num(p.get("price_change_percent"), None)
    if pc is not None and pc >= 80:
        res.append("Price about to rise (meter %+.0f%%)" % pc)
    return res or ["Best projected points for the money"]


def analyse_team(app, entry_id, horizon, ft_override, fresh):
    m = app.model(fresh)
    st = load_squad(app.src, m, entry_id, fresh)
    gws = m.gws(horizon)
    val = m.vals(gws)
    nxt = m.vals([m.first])
    squad = st["squad"]
    xi = pick_xi(squad, val, m.pos_of, cap_val=nxt)
    pools = make_pools(m, val)
    sell = [0] * len(m.pos_of)
    for pid, s in st["sell"].items():
        sell[pid] = s
    base, best = plan_transfers(m, squad, st["bank"], sell, val, pools, max_k=3, beam=20)
    ft = st["ft_est"] if ft_override is None else ft_override
    plans = []
    for k in sorted(best):
        score, ids, bank_after, moves = best[k]
        hits = max(0, k - ft)
        plans.append({
            "k": k, "gain": round(score - base, 1), "hits": hits, "hit_cost": hits * HIT_COST,
            "net": round(score - base - hits * HIT_COST, 1), "bank_after": bank_after,
            "moves": [{"out": m.card(o, val, gws, sell=st["sell"].get(o), buy=st["buy"].get(o)),
                       "in": m.card(i, val, gws), "why_out": why_out(m, o, gws), "why_in": why_in(m, i, gws),
                       "gain": round(val[i] - val[o], 1)} for (o, i) in moves]})
    # each free transfer you use is worth a little less than it looks (you could have banked it), so require a real gain
    def worth(p):
        if not p["k"]:
            return 0.0
        # taking a hit needs a clear margin because projections are uncertain
        return p["net"] - 0.75 * min(p["k"], ft) - (1.5 if p["hits"] else 0.0)
    rec = max(plans, key=lambda p: (worth(p), -p["k"]))
    if rec["k"] and worth(rec) <= 0.5:
        rec = plans[0]
    alerts = []
    for pid in squad:
        p = m.players[pid]
        if p.get("status", "a") != "a" or (p.get("chance_of_playing_next_round") not in (None, 100)):
            alerts.append({"id": pid, "name": p["web_name"], "status": p.get("status"), "news": p.get("news") or "",
                           "chance": p.get("chance_of_playing_next_round")})
    caps = [m.card(i, nxt, gws) for i in sorted(xi["xi"], key=lambda i: -nxt[i])[:3]]
    entry = st["entry"]
    sell_total = sum(st["sell"].values())
    return {
        "manager": ("%s %s" % (entry.get("player_first_name", ""), entry.get("player_last_name", ""))).strip(),
        "team_name": entry.get("name"), "overall_rank": entry.get("summary_overall_rank"),
        "overall_points": entry.get("summary_overall_points"),
        "gw_next": m.first, "gws": gws, "horizon": len(gws), "bank": st["bank"], "value": sell_total,
        "ft": ft, "ft_estimated": ft_override is None, "made_next": st["made_next"],
        "squad": [m.card(i, val, gws, sell=st["sell"].get(i), buy=st["buy"].get(i)) for i in squad],
        "xi": xi["xi"], "bench": xi["bench"], "captain": xi["captain"], "vice": xi["vice"], "formation": xi["formation"],
        "plans": plans, "recommended": rec["k"], "alerts": alerts, "captains": caps,
        "xp_now": round(base, 1),
    }


def build_team(app, budget, horizon, fresh):
    m = app.model(fresh)
    gws = m.gws(horizon)
    val = m.vals(gws)
    nxt = m.vals([m.first])
    pools = make_pools(m, val)
    score, ids = optimise_squad(m, val, budget, pools)
    if ids is None:
        raise UserError("Couldn't build a legal squad for that budget - it's too low.")
    xi = pick_xi(ids, val, m.pos_of, cap_val=nxt)
    cost = sum(m.price[i] for i in ids)
    total = sum(val[i] for i in xi["xi"]) + val[xi["captain"]]
    order = {1: 0, 2: 1, 3: 2, 4: 3}
    ids = sorted(ids, key=lambda i: (order[m.pos_of[i]], -val[i]))
    return {"gw_next": m.first, "gws": gws, "horizon": len(gws), "budget": budget, "cost": cost, "bank": budget - cost,
            "squad": [m.card(i, val, gws) for i in ids], "xi": xi["xi"], "bench": xi["bench"],
            "captain": xi["captain"], "vice": xi["vice"], "formation": xi["formation"], "xp_total": round(total, 1)}


# ----------------------------------------------------------------------------
# Chips
# ----------------------------------------------------------------------------

def chip_states(m, hist):
    """Which chips you still have, from FPL's own chip windows and the chips you've played."""
    windows = [{"name": c.get("name"), "start": int(c.get("start_event") or 1), "stop": int(c.get("stop_event") or m.last_gw)}
               for c in m.chips if c.get("name") in CHIP_LABEL]
    if not windows:
        for (s, e) in ((1, 19), (20, 38)):
            for n in CHIP_ORDER:
                windows.append({"name": n, "start": s, "stop": e})
    windows.sort(key=lambda w: (w["start"], CHIP_ORDER.index(w["name"]) if w["name"] in CHIP_ORDER else 9))
    used = list(hist.get("chips") or [])
    taken = set()
    out = []
    for w in windows:
        u = None
        for i, c in enumerate(used):
            if i not in taken and c.get("name") == w["name"] and w["start"] <= int(c.get("event") or 0) <= w["stop"]:
                u = c
                taken.add(i)
                break
        if u:
            state = "used"
        elif w["stop"] < m.first:
            state = "expired"
        elif w["start"] > m.first:
            state = "locked"
        else:
            state = "available"
        out.append({"name": w["name"], "label": CHIP_LABEL.get(w["name"], w["name"]), "start": w["start"],
                    "stop": w["stop"], "state": state, "used_gw": int(u["event"]) if u else None})
    return out


def analyse_chips(app, entry_id, fresh):
    m = app.model(fresh)
    st = load_squad(app.src, m, entry_id, fresh)
    squad = st["squad"]
    budget = sum(st["sell"].values()) + st["bank"]
    states = chip_states(m, st["hist"])
    ft = st["ft_est"]
    all_gws = list(range(m.first, m.last_gw + 1))
    per_gw = {}
    best_any = {}
    for g in all_gws:
        vg = m.vals([g])
        xi = pick_xi(squad, vg, m.pos_of)
        cap = xi["captain"]
        per_gw[g] = {"xi": sum(vg[i] for i in xi["xi"]) + vg[cap], "bench": sum(vg[i] for i in xi["bench"]),
                     "cap": vg[cap], "cap_name": m.players[cap]["web_name"],
                     "playing": sum(1 for i in squad if m.fx.get((m.team_of[i], g)))}
        top = max((i for i in m.players if m.eligible[i]), key=lambda i: vg[i])
        best_any[g] = (vg[top], m.players[top]["web_name"])
    # candidate gameweeks for the expensive 'build the perfect squad' maths
    open_windows = [s for s in states if s["state"] in ("available",)]
    lo = min([max(s["start"], m.first) for s in open_windows] or [m.first])
    hi = max([min(s["stop"], m.last_gw) for s in open_windows] or [m.first])
    special = [g for g in all_gws if lo <= g <= hi and (len(m.gw_info[g]["blank"]) >= 2 or len(m.gw_info[g]["double"]) >= 2)]
    cands = sorted(set([g for g in all_gws[:2] if lo <= g <= hi] + special))[:8]
    fh_gain, bb_pot = {}, {}
    for g in cands:
        vg = m.vals([g])
        pools = make_pools(m, vg, per_pos=45, cheap=12, extra=10)
        s_fh, ids_fh = optimise_squad(m, vg, budget, pools, iters=14000, restarts=2, bench_w=0.1)
        if ids_fh is not None:
            fh_gain[g] = max(0.0, s_fh - squad_score(squad, vg, m.pos_of, 0.1))
        s_bb, ids_bb = optimise_squad(m, vg, budget, pools, iters=14000, restarts=2, bench_w=1.0)
        if ids_bb is not None:
            bb_pot[g] = sum(vg[i] for i in pick_xi(ids_bb, vg, m.pos_of)["bench"])
    # wildcard: rebuild now for the next 6 gameweeks vs your best use of free transfers
    gws6 = m.gws(6)
    val6 = m.vals(gws6)
    pools6 = make_pools(m, val6)
    sell = [0] * len(m.pos_of)
    for pid, s in st["sell"].items():
        sell[pid] = s
    opt6, ids6 = optimise_squad(m, val6, budget, pools6, iters=30000, restarts=2)
    base6, best6 = plan_transfers(m, squad, st["bank"], sell, val6, pools6, max_k=3, beam=15)
    cur6 = max(best6[k][0] for k in best6 if k <= max(ft, 0))
    wc_gain = max(0.0, (opt6 - cur6) if ids6 else 0.0)
    wc_changes = len(set(ids6) - set(squad)) if ids6 else 0
    unavailable = sum(1 for i in squad if m.players[i].get("status") in ("i", "s", "u", "n")
                      or (m.players[i].get("chance_of_playing_next_round") or 100) < 50)

    def gw_note(g):
        info = m.gw_info[g]
        bits = []
        if info["blank"]:
            bits.append("%d teams blank" % len(info["blank"]))
            bits.append("%d of your players have no game" % (15 - per_gw[g]["playing"]))
        if info["double"]:
            bits.append("%d teams play twice" % len(info["double"]))
        return ", ".join(bits) or "normal gameweek"

    chips_out = []
    for s in states:
        row = dict(s)
        row["options"] = []
        row["verdict"] = s["state"]
        row["headline"] = ""
        if s["state"] == "used":
            row["headline"] = "Used in GW%d." % s["used_gw"]
        elif s["state"] == "expired":
            row["headline"] = "Expired unused."
        elif s["state"] == "locked":
            row["headline"] = "Opens at GW%d." % s["start"]
        else:
            a, b = max(s["start"], m.first), min(s["stop"], m.last_gw)
            name = s["name"]
            if name == "wildcard":
                opts = [{"gw": m.first, "gain": round(wc_gain, 1),
                         "note": "Rebuilding now would change %d players" % wc_changes}]
                left = s["stop"] - m.first
                if left <= 1:
                    row["verdict"], row["headline"] = "use_soon", "Use it by GW%d - it expires after that deadline." % s["stop"]
                elif wc_gain >= 25 or (unavailable >= 4 and wc_gain >= 15):
                    row["verdict"], row["headline"] = "play_now", "Strong case to play it now: about +%.0f pts over the next %d gameweeks." % (wc_gain, len(gws6))
                elif wc_gain >= 12:
                    row["verdict"], row["headline"] = "consider", "Worth considering: about +%.0f pts over %d gameweeks vs your free transfers." % (wc_gain, len(gws6))
                else:
                    row["verdict"], row["headline"] = "hold", "Hold for now: only about +%.0f pts over %d gameweeks. Use it by GW%d." % (wc_gain, len(gws6), s["stop"])
            elif name == "freehit":
                opts = [{"gw": g, "gain": round(v, 1), "note": gw_note(g)} for g, v in fh_gain.items() if a <= g <= b and g > 1]
            elif name == "bboost":
                opts = [{"gw": g, "gain": round(v, 1), "note": "%s. Your bench now: %.1f pts." % (gw_note(g), per_gw[g]["bench"])}
                        for g, v in bb_pot.items() if a <= g <= b]
                # also consider the gameweeks where your current bench is already strong
                for g in all_gws:
                    if a <= g <= b and g not in bb_pot and per_gw[g]["bench"] >= 9:
                        opts.append({"gw": g, "gain": round(per_gw[g]["bench"], 1), "note": "Your bench now: %.1f pts." % per_gw[g]["bench"]})
            elif name == "3xc":
                opts = [{"gw": g, "gain": round(per_gw[g]["cap"], 1),
                         "note": "%s (best in game: %s %.1f). %s" % (per_gw[g]["cap_name"], best_any[g][1], best_any[g][0], gw_note(g))}
                        for g in all_gws if a <= g <= b]
            else:
                opts = []
            if name != "wildcard":
                opts.sort(key=lambda o: -o["gain"])
            row["options"] = opts[:3] if name != "wildcard" else opts
        chips_out.append(row)
    # one chip per gameweek: give each chip its best option that another chip hasn't already claimed
    taken = {}
    ranked = sorted([c for c in chips_out if c["state"] == "available" and c["options"]],
                    key=lambda c: -(c["options"][0]["gain"] if c["name"] != "wildcard" or c["verdict"] in ("play_now", "use_soon") else 0))
    for c in ranked:
        pick = None
        for o in c["options"]:
            if o["gw"] not in taken:
                pick = o
                break
        if pick:
            pick["best"] = True
            taken[pick["gw"]] = c["name"]
            if c["name"] != "wildcard":
                g = pick["gw"]
                v = pick["gain"]
                if c["name"] == "freehit":
                    if v >= 15:
                        c["verdict"], c["headline"] = "good", "Best week: GW%d (about +%.0f pts over your current squad)." % (g, v)
                    else:
                        c["verdict"], c["headline"] = "wait", "No standout week yet (best is GW%d at about +%.0f). Save it for a blank or double gameweek." % (g, v)
                elif c["name"] == "bboost":
                    dg = len(m.gw_info[g]["double"]) >= 4
                    if v >= 18 or (dg and v >= 12):
                        c["verdict"], c["headline"] = "good", "Best week: GW%d - a bench built for it could score about %.0f pts." % (g, v)
                    else:
                        c["verdict"], c["headline"] = "wait", "No big double gameweek in range yet (best is GW%d, about %.0f). Plan it after a Wildcard or for a double." % (g, v)
                elif c["name"] == "3xc":
                    if v >= 10:
                        c["verdict"], c["headline"] = "good", "Best week: GW%d - %s is projected %.1f pts, so Triple Captain adds about that much." % (g, per_gw[g]["cap_name"], v)
                    else:
                        c["verdict"], c["headline"] = "wait", "Best so far is GW%d (%.1f pts from the captain). Double gameweeks for a premium player are the sweet spot." % (g, v)
    for c in chips_out:
        if c["state"] == "available" and not c["headline"]:
            c["verdict"], c["headline"] = "wait", "Nothing stands out yet - keep it for a blank or double gameweek."
    table = []
    for g in all_gws[:10]:
        info = m.gw_info[g]
        table.append({"gw": g, "fixtures": info["fixtures"], "blank": len(info["blank"]), "double": len(info["double"]),
                      "deadline": (m.events[g] or {}).get("deadline_time"), "xi": round(per_gw[g]["xi"], 1),
                      "bench": round(per_gw[g]["bench"], 1), "cap": round(per_gw[g]["cap"], 1),
                      "cap_name": per_gw[g]["cap_name"], "playing": per_gw[g]["playing"],
                      "fh": round(fh_gain[g], 1) if g in fh_gain else None, "bb": round(bb_pot[g], 1) if g in bb_pot else None})
    specials = [{"gw": g, "blank": len(m.gw_info[g]["blank"]), "double": len(m.gw_info[g]["double"])}
                for g in all_gws if len(m.gw_info[g]["blank"]) >= 2 or len(m.gw_info[g]["double"]) >= 2]
    return {"gw_next": m.first, "chips": chips_out, "table": table, "specials": specials, "ft": ft,
            "unavailable": unavailable, "budget": budget}


# ----------------------------------------------------------------------------
# Phone support: home-screen icon, web-app manifest, finding this computer's Wi-Fi address
# ----------------------------------------------------------------------------

MANIFEST = {"name": "FPL Assistant", "short_name": "FPL Assist", "start_url": "/", "scope": "/",
            "display": "standalone", "background_color": "#10111b", "theme_color": "#3d0a4f",
            "icons": [{"src": "/icon.png", "sizes": "192x192", "type": "image/png", "purpose": "any"}]}
_ICON = {}


def make_icon(size=192):
    """A simple football-pitch icon as PNG bytes (drawn by hand, so no image library is needed)."""
    if size in _ICON:
        return _ICON[size]
    margin, line = 0.14, 0.024

    def box(x, y, cx, cy, hw, hh):                      # distance to the outline of a rectangle
        qx, qy = abs(x - cx) - hw, abs(y - cy) - hh
        return abs(math.hypot(max(qx, 0.0), max(qy, 0.0)) + min(max(qx, qy), 0.0))

    raw = bytearray()
    for j in range(size):
        y = (j + 0.5) / size
        raw.append(0)                                   # PNG filter byte for this row
        for i in range(size):
            x = (i + 0.5) / size
            r, g, b = (28, 128, 70) if int(x * 8) % 2 else (36, 146, 82)
            d = box(x, y, 0.5, 0.5, 0.5 - margin, 0.5 - margin)
            if abs(x - 0.5) <= 0.5 - margin:
                d = min(d, abs(y - 0.5))                # halfway line
            d = min(d, abs(math.hypot(x - 0.5, y - 0.5) - 0.17))                        # centre circle
            d = min(d, box(x, y, 0.5, margin + 0.09, 0.23, 0.09), box(x, y, 0.5, 1 - margin - 0.09, 0.23, 0.09))
            a = clamp(0.5 + (line / 2 - d) * size, 0.0, 1.0)
            a = max(a, clamp(0.5 + (0.035 - math.hypot(x - 0.5, y - 0.5)) * size, 0.0, 1.0)) * 0.93   # centre spot
            raw += bytes((int(r + (255 - r) * a), int(g + (255 - g) * a), int(b + (255 - b) * a)))

    def chunk(tag, data):
        return struct.pack(">I", len(data)) + tag + data + struct.pack(">I", zlib.crc32(tag + data) & 0xffffffff)
    png = (b"\x89PNG\r\n\x1a\n" + chunk(b"IHDR", struct.pack(">IIBBBBB", size, size, 8, 2, 0, 0, 0)) +
           chunk(b"IDAT", zlib.compress(bytes(raw), 9)) + chunk(b"IEND", b""))
    _ICON[size] = png
    return png


def lan_ip():
    """This computer's address on the local network (what a phone on the same Wi-Fi should type)."""
    s = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    try:
        s.connect(("10.255.255.255", 1))                # no data is actually sent
        ip = s.getsockname()[0]
        return None if ip.startswith("127.") else ip
    except OSError:
        return None
    finally:
        s.close()


# ----------------------------------------------------------------------------
# The local web server
# ----------------------------------------------------------------------------

class App(object):
    def __init__(self, src, demo=False):
        self.src = src
        self.demo = demo
        self._model = None
        self._key = None
        self._lock = threading.Lock()
        self._memo = {}
        self.phone_url = None

    def model(self, fresh=False):
        bs = self.src.get("bootstrap-static/", ttl=120, force=fresh)
        fx = self.src.get("fixtures/", ttl=600, force=fresh)
        key = (self.src.stamp("bootstrap-static/"), self.src.stamp("fixtures/"))
        with self._lock:
            if self._model is None or key != self._key:
                self._model = Model(bs, fx)
                self._key = key
            return self._model

    def memo(self, key, ttl, fn, fresh=False):
        self.model(fresh)
        now = time.time()
        with self._lock:
            hit = self._memo.get(key)
            cur = self._key
        if hit and not fresh and now - hit[0] < ttl and hit[2] == cur:
            return hit[1]
        data = fn()
        with self._lock:
            self._memo[key] = (time.time(), data, self._key)
        return data

    def status(self, fresh=False):
        m = self.model(fresh)
        return {"mode": "demo" if self.demo else "live", "fetched_at": self.src.stamp("bootstrap-static/"),
                "gw_next": m.first, "gw_current": m.current,
                "deadline": (m.events[m.first] or {}).get("deadline_time"),
                "price_deadlines": m.price_deadlines, "price_updated": m.price_updated,
                "players": len(m.players), "managers": m.total_managers, "ft_cap": m.ft_cap, "last_gw": m.last_gw,
                "phone_url": self.phone_url}

    def players(self, horizon, fresh=False):
        m = self.model(fresh)
        gws = m.gws(horizon)
        val = m.vals(gws)
        out = []
        for pid, p in m.players.items():
            out.append({"id": pid, "n": p.get("web_name"), "t": m.teams[p["team"]]["short_name"], "p": p["element_type"],
                        "c": int(p["now_cost"]), "cs": int(p.get("cost_change_start") or 0),
                        "ce": int(p.get("cost_change_event") or 0), "o": num(p.get("selected_by_percent")),
                        "f": num(p.get("form")), "tp": int(num(p.get("total_points"))), "m": int(num(p.get("minutes"))),
                        "x1": round(m.xp[pid].get(m.first, 0.0), 1), "xh": round(val[pid], 1),
                        "fx": m.fixture_list(p["team"], gws[:3]), "s": p.get("status", "a"), "nw": p.get("news") or "",
                        "ch": p.get("chance_of_playing_next_round"), "pc": num(p.get("price_change_percent"), None),
                        "pj": Model.price_proj(p), "lk": p.get("price_change_locked_until"),
                        "ni": int(num(p.get("transfers_in_event")) - num(p.get("transfers_out_event"))),
                        "ok": bool(m.eligible[pid])})
        return {"players": out, "gw_next": m.first, "gws": gws,
                "teams": sorted(set(t["short_name"] for t in m.teams.values()))}

    def fixtures(self, n, fresh=False):
        m = self.model(fresh)
        gws = list(range(m.first, min(m.last_gw, m.first + n - 1) + 1))
        teams = [{"id": tid, "name": t["name"], "short": t["short_name"], "rows": m.fixture_list(tid, gws),
                  "avg": m.avg_fdr(tid, gws[:5])} for tid, t in m.teams.items()]
        teams.sort(key=lambda t: t["name"])
        return {"gws": gws, "teams": teams,
                "info": dict((g, {"blank": len(m.gw_info[g]["blank"]), "double": len(m.gw_info[g]["double"])}) for g in gws)}


def qint(q, key, default, lo, hi):
    try:
        v = int(float(q.get(key, default)))
    except (TypeError, ValueError):
        v = default
    return max(lo, min(hi, v))


class Handler(BaseHTTPRequestHandler):
    app = None
    server_version = "FPLAssistant/1.0"

    def log_message(self, fmt, *args):
        pass

    def _send(self, code, body, ctype):
        data = body.encode("utf-8") if isinstance(body, str) else body
        self.send_response(code)
        self.send_header("Content-Type", ctype)
        self.send_header("Content-Length", str(len(data)))
        self.send_header("Cache-Control", "no-store")
        self.end_headers()
        self.wfile.write(data)

    def _json(self, obj, code=200):
        self._send(code, json.dumps(obj), "application/json; charset=utf-8")

    def do_HEAD(self):                       # some hosts/health checkers send HEAD
        self.send_response(200)
        self.send_header("Content-Length", "0")
        self.end_headers()

    def do_GET(self):
        url = urlparse(self.path)
        q = dict((k, v[0]) for k, v in parse_qs(url.query).items())
        fresh = q.get("fresh") == "1"
        app = self.app
        try:
            if url.path in ("/", "/index.html"):
                return self._send(200, PAGE, "text/html; charset=utf-8")
            if url.path == "/healthz":
                return self._send(200, "ok", "text/plain")
            if url.path == "/manifest.webmanifest":
                return self._send(200, json.dumps(MANIFEST), "application/manifest+json")
            if url.path in ("/icon.png", "/favicon.ico"):
                return self._send(200, make_icon(), "image/png")
            if url.path == "/api/status":
                return self._json(app.status(fresh))
            if url.path == "/api/players":
                return self._json(app.players(qint(q, "h", 5, 1, 12), fresh))
            if url.path == "/api/fixtures":
                return self._json(app.fixtures(qint(q, "n", 8, 3, 12), fresh))
            if url.path == "/api/build":
                try:
                    budget = int(round(float(q.get("budget", "100")) * 10))
                except ValueError:
                    raise UserError("Budget must be a number like 100.0")
                budget = max(600, min(2000, budget))
                h = qint(q, "h", 5, 1, 12)
                return self._json(app.memo(("build", budget, h), 120, lambda: build_team(app, budget, h, fresh), fresh))
            if url.path in ("/api/team", "/api/chips"):
                eid = qint(q, "id", 0, 0, 10 ** 10)
                if not eid:
                    raise UserError("Enter your FPL team ID first (it's the number in the URL of your Points page).")
                if url.path == "/api/chips":
                    return self._json(app.memo(("chips", eid), 180, lambda: analyse_chips(app, eid, fresh), fresh))
                h = qint(q, "h", 5, 1, 12)
                ft = qint(q, "ft", -1, -1, 5)
                ft = None if ft < 0 else ft
                return self._json(app.memo(("team", eid, h, ft), 120, lambda: analyse_team(app, eid, h, ft, fresh), fresh))
            self._send(404, "Not found", "text/plain")
        except UserError as e:
            self._json({"error": str(e)}, 400)
        except NotFound as e:
            self._json({"error": str(e)}, 404)
        except FPLError as e:
            self._json({"error": str(e)}, 502)
        except (BrokenPipeError, ConnectionResetError):
            pass
        except Exception as e:                     # a bug on our side - show it rather than hang
            traceback.print_exc()
            self._json({"error": "Something went wrong inside the app: %s" % e}, 500)


def main():
    global EFFORT
    ap = argparse.ArgumentParser(description="FPL Assistant - a local Fantasy Premier League helper")
    ap.add_argument("--port", type=int, default=8765, help="port for the local web page (default 8765)")
    ap.add_argument("--demo", action="store_true", help="use fake demo data instead of the live FPL feed")
    ap.add_argument("--no-browser", action="store_true", help="don't open the browser automatically")
    ap.add_argument("--share", action="store_true",
                    help="let your phone (on the same Wi-Fi) open the app; prints the address to use")
    args = ap.parse_args()
    env_port = os.environ.get("PORT", "")
    hosted = env_port.isdigit()              # web hosts such as Render tell the app which port to listen on
    port = int(env_port) if hosted else args.port
    if hosted:
        EFFORT = 0.5                         # shared free servers are slow, so search a little less
        args.no_browser = True
    app = App(Source(fetcher=make_demo_fetcher() if args.demo else None), demo=args.demo)
    Handler.app = app
    try:
        server = ThreadingHTTPServer(("0.0.0.0" if (args.share or hosted) else "127.0.0.1", port), Handler)
    except OSError as e:
        print("Couldn't start on port %d (%s). Close the other copy or try:  python fpl_assistant.py --port 8800" % (port, e))
        return 1
    server.daemon_threads = True
    url = "http://localhost:%d" % port

    def warm():
        try:
            m = app.model()
            print("Loaded %d players. Next gameweek: GW%d.%s" % (len(m.players), m.first, "  [DEMO DATA]" if args.demo else ""))
        except FPLError as e:
            print("Heads up: %s" % e)
        except Exception as e:
            traceback.print_exc()
    threading.Thread(target=warm, daemon=True).start()
    if hosted:
        print("FPL Assistant is running in hosted mode on port %d." % port)
    else:
        print("FPL Assistant is running at %s   (press Ctrl+C to stop)" % url)
    if args.share and not hosted:
        ip = lan_ip()
        if ip:
            app.phone_url = "http://%s:%d" % (ip, port)
            print("ON YOUR PHONE (same Wi-Fi), open:  %s" % app.phone_url)
            print("Anyone on your Wi-Fi can open that address while this window is running.")
            print("If Windows asks about the firewall, choose 'Allow' for private networks.")
        else:
            print("Couldn't work out this computer's Wi-Fi address - check that you're connected to a network.")
    if not args.no_browser:
        threading.Timer(0.8, lambda: webbrowser.open(url)).start()
    try:
        server.serve_forever()
    except KeyboardInterrupt:
        print("\nBye!")
    return 0



# ----------------------------------------------------------------------------
# Demo data (fake clubs and players) so you can try the app offline: --demo
# ----------------------------------------------------------------------------

DEMO_ENTRY_ID = 1234567


def _round_robin(n):
    arr = list(range(1, n + 1))
    rounds = []
    for r in range(n - 1):
        pairs = []
        for i in range(n // 2):
            a, b = arr[i], arr[n - 1 - i]
            pairs.append((a, b) if (r + i) % 2 == 0 else (b, a))
        rounds.append(pairs)
        arr = [arr[0]] + [arr[-1]] + arr[1:-1]
    return rounds + [[(b, a) for (a, b) in rd] for rd in rounds]


def make_demo_fetcher():
    rnd = random.Random(2026)
    now = datetime.now(timezone.utc)
    iso = lambda d: d.strftime("%Y-%m-%dT%H:%M:%SZ")
    names = ["Ashford", "Brenton", "Carlow", "Dunmere", "Eastvale", "Fenwick", "Garston", "Hallam", "Ironbridge",
             "Kingsley", "Larkfield", "Marston", "Northgate", "Oakham", "Pemberton", "Queensway", "Rothley",
             "Stanmore", "Thornbury", "Upton"]
    surnames = ["Walker", "Reid", "Hughes", "Patel", "Morgan", "Doyle", "Nakamura", "Silva", "Okafor", "Lindqvist",
                "Brandt", "Costa", "Mendes", "Novak", "Fraser", "Keane", "Lopez", "Mbeki", "Ward", "Hale", "Ito",
                "Rossi", "Duarte", "Kerr", "Boyd", "Flynn", "Vega", "Osei", "Larsen", "Marsh", "Cole", "Nash"]
    teams, quality = [], {}
    for i, n in enumerate(names, 1):
        quality[i] = clamp(rnd.gauss(1.0, 0.16), 0.7, 1.4)
        teams.append({"id": i, "code": i, "name": n + " Demo", "short_name": n[:3].upper(), "strength": None,
                      "strength_overall_home": 3, "strength_overall_away": 3, "strength_attack_home": 0,
                      "strength_attack_away": 0, "strength_defence_home": 0, "strength_defence_away": 0})
    cur, nxt = 6, 7
    events = []
    for g in range(1, 39):
        dl = now + timedelta(days=2) + timedelta(days=7 * (g - nxt))
        events.append({"id": g, "name": "Gameweek %d" % g, "deadline_time": iso(dl), "finished": g <= cur,
                       "is_current": g == cur, "is_next": g == nxt, "is_previous": g == cur - 1})
    chips = []
    cid = 1
    for (s, e) in ((1, 19), (20, 38)):
        for name in ("wildcard", "freehit", "bboost", "3xc"):
            chips.append({"id": cid, "name": name, "number": 1, "start_event": max(s, 2 if name in ("wildcard", "freehit") else s),
                          "stop_event": e})
            cid += 1
    # fixtures (GW12 loses 4 matches which are replayed in GW13 -> blank + double)
    rounds = _round_robin(20)
    fixtures, fid = [], 1
    moved = rounds[11][:4]
    rounds[11] = rounds[11][4:]
    rounds[12] = rounds[12] + moved
    for gw, pairs in enumerate(rounds, 1):
        for (h, a) in pairs:
            def diff(opp, home):
                return int(clamp(round(2.2 + (quality[opp] - 1.0) * 5 + (-0.4 if home else 0.4)), 2, 5))
            fixtures.append({"id": fid, "event": gw, "team_h": h, "team_a": a, "finished": gw <= cur,
                             "kickoff_time": iso(events[gw - 1]["deadline_time"] and (parse_time(events[gw - 1]["deadline_time"]) + timedelta(days=1))),
                             "team_h_difficulty": diff(a, True), "team_a_difficulty": diff(h, False)})
            fid += 1
    # players
    span = {1: 2.5, 2: 4.0, 3: 9.0, 4: 8.5}
    base = {1: 4.0, 2: 4.0, 3: 4.5, 4: 4.5}
    layout = {1: (1, 1, 1), 2: (5, 3, 1), 3: (5, 4, 1), 4: (3, 2, 1)}   # starters, backups, fringe per position
    elements, pid = [], 0
    for t in teams:
        tq = quality[t["id"]]
        for pos, (ns, nb, nf) in layout.items():
            for k in range(ns + nb + nf):
                pid += 1
                role = "start" if k < ns else ("rot" if k < ns + nb else "fringe")
                skill = math.exp(rnd.gauss(0, 0.28)) * tq
                price = base[pos] + clamp((skill - 0.6) / 1.4, 0, 1.0) * span[pos]
                if role != "start":
                    price = clamp(price - 0.8, base[pos], 20)
                price = int(round(price * 10))
                true = max(1.0, prior_pp90(pos, price / 10.0) * math.exp(rnd.gauss(0, 0.2)))
                mins, pts, starts = 0, 0.0, 0
                for g in range(cur):
                    if role == "start":
                        m = 90 if rnd.random() < 0.85 else (60 if rnd.random() < 0.5 else 0)
                    elif role == "rot":
                        m = 75 if rnd.random() < 0.35 else (20 if rnd.random() < 0.3 else 0)
                    else:
                        m = 15 if rnd.random() < 0.08 else 0
                    mins += m
                    starts += 1 if m >= 60 else 0
                    pts += max(0.0, true * m / 90.0 + rnd.gauss(0, 1.6) * (m / 90.0)) if m else 0.0
                pts = int(round(pts))
                goals = int(round(pts * (0.0 if pos == 1 else (0.12 if pos == 2 else 0.3)) / GOAL_PTS[pos]))
                assists = int(round(pts * (0.05 if pos == 2 else 0.18) / 3.0)) if pos > 1 else 0
                gk_xgc = round(mins / 90.0 * 1.35 / quality[t["id"]], 2)
                status, chance, news = "a", None, ""
                roll = rnd.random()
                if role == "start" and roll < 0.07:
                    status, chance, news = "d", rnd.choice([25, 50, 75]), "Knock - %d%% chance of playing"
                    news = news % chance
                elif role == "start" and roll < 0.10:
                    status, chance = "i", 0
                    news = rnd.choice(["Hamstring injury - Expected back %d Nov" % rnd.randint(2, 28), "Knee injury - Unknown return date"])
                elif role == "start" and roll < 0.11:
                    status, chance, news = "s", 0, "Suspended until %d Nov" % rnd.randint(1, 9)
                pcp = clamp(rnd.gauss(0, 45), -110, 110)
                proj = [{"offset": o, "projected_percent": "%.1f" % (pcp + o * rnd.gauss(4, 3)), "likelihood": 1} for o in range(3)]
                elements.append({
                    "id": pid, "web_name": "%s %d" % (rnd.choice(surnames), pid), "first_name": "Demo", "second_name": "Player",
                    "team": t["id"], "team_code": t["id"], "element_type": pos, "now_cost": price,
                    "cost_change_start": rnd.choice([-2, -1, 0, 0, 1, 2, 3]), "cost_change_event": rnd.choice([0, 0, 0, 1, -1]),
                    "status": status, "chance_of_playing_next_round": chance, "chance_of_playing_this_round": chance,
                    "news": news, "form": "%.1f" % max(0.0, rnd.gauss(true * 0.75, 1.8)),
                    "points_per_game": "%.1f" % (pts / max(starts, 1) if mins else 0), "total_points": pts, "minutes": mins,
                    "starts": starts, "goals_scored": goals, "assists": assists,
                    "expected_goals": "%.2f" % (goals * math.exp(rnd.gauss(0, 0.3)) + (0.0 if pos == 1 else 0.05)),
                    "expected_assists": "%.2f" % (assists * math.exp(rnd.gauss(0, 0.3)) + (0.0 if pos == 1 else 0.05)),
                    "expected_goals_conceded": "%.2f" % (gk_xgc if pos == 1 else 0),
                    "selected_by_percent": "%.1f" % clamp(rnd.gauss(8, 12) * skill, 0.1, 55),
                    "transfers_in_event": int(abs(rnd.gauss(0, 30000))), "transfers_out_event": int(abs(rnd.gauss(0, 30000))),
                    "price_change_percent": "%.1f" % pcp, "price_change_projections": proj,
                    "price_change_locked_until": None, "can_select": True, "can_transact": True, "removed": False})
    for e in elements:                     # make the likelihood labels roughly consistent
        for pj in e["price_change_projections"]:
            v = abs(float(pj["projected_percent"]))
            lv = 5 if v >= 100 else 4 if v >= 95 else 3 if v >= 50 else 2 if v >= 20 else 1
            pj["likelihood"] = lv if float(pj["projected_percent"]) >= 0 else -lv
    for e in elements[:6]:
        e.update({"status": "u", "can_select": False, "chance_of_playing_next_round": 0, "news": "Has left the club"})
    deadlines = [iso((now + timedelta(days=d)).replace(hour=23, minute=0, second=0)) for d in range(3)]
    bootstrap = {"chips": chips, "events": events, "teams": teams, "elements": elements, "total_players": 11083924,
                 "game_settings": {"squad_total_spend": 1000, "squad_team_limit": 3, "max_extra_free_transfers": 4},
                 "game_config": {"settings": {"price_change_deadlines": deadlines},
                                 "status": {"price_change_last_updated": iso(now - timedelta(hours=1))}}}
    by_id = {e["id"]: e for e in elements}

    # a demo manager: expensive but mediocre squad built from "total points" with 2 flagged players
    need = [1] * 2 + [2] * 5 + [3] * 5 + [4] * 3
    squad, cost, cnt = [], 0, Counter()
    ranked = sorted([e for e in elements if e["status"] in ("a", "d")], key=lambda e: -e["total_points"])
    for idx, p in enumerate(need):
        rest = 46 * (len(need) - idx - 1)
        for e in ranked:
            if e["element_type"] == p and e["id"] not in squad and cnt[e["team"]] < 3 and cost + e["now_cost"] + rest <= 996:
                squad.append(e["id"]); cost += e["now_cost"]; cnt[e["team"]] += 1
                break
    for pidx in (3, 9):
        by_id[squad[pidx]].update({"status": "i", "chance_of_playing_next_round": 0, "news": "Ankle injury - Expected back 8 Nov"})
    bank = 1000 - cost
    transfers = []
    for k, pidx in enumerate((4, 10)):
        e = by_id[squad[pidx]]
        old = [x for x in elements if x["element_type"] == e["element_type"] and x["id"] not in squad][k]
        transfers.append({"element_in": e["id"], "element_in_cost": e["now_cost"] - 3, "element_out": old["id"],
                          "element_out_cost": old["now_cost"], "entry": DEMO_ENTRY_ID, "event": 3 + k,
                          "time": iso(now - timedelta(days=30 - 7 * k))})
    entry = {"id": DEMO_ENTRY_ID, "player_first_name": "Demo", "player_last_name": "Manager", "name": "Demo FC",
             "started_event": 1, "current_event": cur, "summary_overall_points": 380, "summary_overall_rank": 2412345,
             "last_deadline_bank": bank, "last_deadline_value": cost}
    history = {"current": [{"event": g, "points": 50, "total_points": 50 * g, "bank": bank, "value": cost,
                            "event_transfers": 0 if g == 1 else (1 if g in (3, 4) else 0), "event_transfers_cost": 0}
                           for g in range(1, cur + 1)],
               "past": [], "chips": [{"name": "bboost", "event": 1, "time": iso(now - timedelta(days=40))}]}
    picks = {"active_chip": None, "automatic_subs": [],
             "entry_history": {"event": cur, "bank": bank, "value": cost, "event_transfers": 0},
             "picks": [{"element": i, "position": n + 1, "multiplier": 1, "is_captain": n == 0, "is_vice_captain": n == 1,
                        "element_type": by_id[i]["element_type"]} for n, i in enumerate(squad)]}

    def fetch(path):
        if path == "bootstrap-static/":
            return bootstrap
        if path == "fixtures/":
            return fixtures
        mt = re.match(r"entry/(\d+)/(.*)$", path)
        if mt:
            rest = mt.group(2)
            if rest == "":
                return entry
            if rest == "history/":
                return history
            if rest == "transfers/":
                return transfers
            if re.match(r"event/\d+/picks/$", rest):
                return picks
        raise NotFound("Demo mode has no data for " + path + " (try team ID %d)." % DEMO_ENTRY_ID)
    return fetch


if __name__ == "__main__":
    sys.exit(main())
