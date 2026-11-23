#!/usr/bin/env python3
"""mem-search.py —— 本地 Markdown 经验资产全文检索（.learnings + memory 统一索引）。

为什么需要它（2026-11-23，学习 agentic-os 后自评的结论）：
    铁律与事故复盘都已落盘（Claw .learnings 350 篇 + 各仓 memory 605 篇），
    但「排查时想不起来去查」导致同类问题反复犯。缺的不是写，是**检索**。
    本脚本是经验闭环（incident-triage → .learnings → 周度升级）最后一公里的检索层。

设计取舍：
- 零依赖：只用标准库 sqlite3，单文件索引，无服务无端口，随时可删（rm 库即回滚）。
- 中文分词：FTS5 默认 unicode61 把整句当一个 token，trigram 又要求查询 ≥3 字
  （「止损」「仓位」「复盘」这类 2 字高频词全失效，实测 trigram match '止损' 返回空）。
  故采用**单字切分 + phrase 查询**：'止损' → "止 损"，可精确子串匹配任意长度词。
- 索引落内盘 ~/.local/var/，不进外置卷（后台任务读外置卷会 TCC EPERM）。

能力（每条均有 self-test 或 verify 覆盖）：
    index     增量索引；--full 全量重建。扫描目录整体不可见时**保留旧索引并告警**
    query     正文检索；多词为行内共现 AND；查询前自动增量刷新
    similar   写新经验前查重；文本相似度 + 稀有种子覆盖双口径
    stats     索引规模与最新覆盖
    self-test 自检（分词/截断/掉线保护/查重端到端）
    verify    交付前总闸：自检 + 文档命令与实现一致性 + 索引健康（含源库逐段比对）
              + 版本控制 + 异地副本（--strict：告警项也视为失败，交付前用）

用法:
    mem-search.py index
    mem-search.py index --full
    mem-search.py query 止损 仓位
    mem-search.py query 告警 --kind learnings --limit 5
    mem-search.py similar /tmp/新草稿.md
    mem-search.py stats
    mem-search.py self-test
    mem-search.py verify
    mem-search.py verify --strict

退出码: 0 正常 ｜ 1 无命中 / 自检失败 ｜ 2 参数或环境错误
        ｜ 3 索引不完整（目录不可见或文件读不到）｜ 4 查重命中重复
回滚: rm -f ~/.local/var/mem-search.db
"""
from __future__ import annotations

import argparse
import json
import os
import random
import re
import sqlite3
import subprocess
import sys
import time
from pathlib import Path

DB_PATH = Path.home() / ".local" / "var" / "mem-search.db"
SKILL_PATH = Path.home() / ".workbuddy" / "skills" / "mem-search" / "SKILL.md"
MAX_FILE_BYTES = 4 * 1024 * 1024
MAX_LINE_CHARS = 2000  # 超长行按此切片（切片而非丢弃，避免漏检长行尾部）

# 白名单扫描根（相对 $HOME）。只收「经验/规则/记忆」，不收 docs/output 噪音。
SCAN_ROOTS: list[tuple[str, str]] = [
    ("WorkBuddy/*/.learnings", "learnings"),
    ("WorkBuddy/*/.workbuddy/memory", "memory"),
]
USER_MEMORY_FILES = ("MEMORY.md", "SOUL.md", "USER.md", "IDENTITY.md", "EVIDENCE.md", "RESTORE.md")
SKIP_DIR_PARTS = {
    ".git", "node_modules", "__pycache__", ".venv", "venv", ".backups",
}
# .backups = 旧快照目录。2026-11-23 实测它与正文同内容，进索引会让同一结论出现两份
# （如 2026-08-02.md 与其 .backups/pre-delete-* 副本同命中）。排除后正文仍可命中，不丢信息。

CJK = r"\u3400-\u4dbf\u4e00-\u9fff\uf900-\ufaff"
TOKEN_RE = re.compile(rf"[{CJK}]|[A-Za-z0-9_]+")
# 注意：不设「查询串白名单」——曾用 ^[A-Za-z0-9_CJK\s]+$ 整体校验，把 pre-commit / v1.2.0 /
# T-INS-xxx / 2026-11-23 这类带连字符和点的查询整条拒掉（2026-11-23 实测：grep 168 处
# pre-commit，CLI 零命中，错误还被 2>/dev/null 吞了）。安全性由 seg() 保证：
# 它只输出 [a-z0-9 中文 空格]，且一律包成双引号 phrase，不含任何 FTS5 语法字符。


def seg(text: str) -> str:
    """切分为 FTS token 序列：中文逐字，ASCII 整词，统一小写。"""
    return " ".join(m.group(0).lower() for m in TOKEN_RE.finditer(text))


def build_match(query_text: str) -> str:
    """把用户查询转为 FTS5 MATCH 表达式：每词 <-> 单字 phrase，词间 AND。"""
    terms = [t for t in query_text.strip().split() if t]
    parts = []
    for term in terms:
        cut = seg(term)
        if cut:
            parts.append('"' + cut + '"')
    return " AND ".join(parts)


def build_match_any(terms: list[str]) -> str:
    """词间 OR（查重用：命中任意种子即入选候选）。"""
    parts = []
    for term in terms:
        cut = seg(term)
        if cut:
            parts.append('"' + cut + '"')
    return " OR ".join(parts)


STOP_TOKENS = {
    "the", "and", "for", "with", "that", "this", "from", "not", "are", "was",
    "http", "https", "www", "com", "json", "true", "false", "null",
}


def extract_seeds(text: str, top: int = 10) -> list[str]:
    """取草稿里最有区分度的检索种子：ASCII 词(len>=3) + 中文二元**字符片段**，按权重排序。

    中文用二元组而非三元组：没有分词器时二元组会跨词边界（'可迁'、'一控'），看着像噪音，
    但召回明显更好——实测同一主题的改写稿，二元组覆盖率 70%、三元组只有 10%。
    查重宁可多报让人来读，不可漏报。
    """
    tokens = [m.group(0) for m in TOKEN_RE.finditer(text.lower())]
    freq: dict[str, float] = {}
    for i, tok in enumerate(tokens):
        if tok.isascii():
            if len(tok) >= 3 and tok not in STOP_TOKENS:
                freq[tok] = freq.get(tok, 0) + 1.0
        elif i + 1 < len(tokens) and len(tokens[i + 1]) == 1 and not tokens[i + 1].isascii():
            bigram = tok + tokens[i + 1]
            freq[bigram] = freq.get(bigram, 0) + 2.0
    return [w for w, _ in sorted(freq.items(), key=lambda kv: (-kv[1], kv[0]))[:top]]


def shingles(text: str, n: int = 3) -> set[str]:
    """字符 n-gram 集合（去空白、小写），用于跨语言通用的相似度计算。"""
    flat = re.sub(r"\s+", "", text.lower())
    if len(flat) < n:
        return {flat} if flat else set()
    return {flat[i : i + n] for i in range(len(flat) - n + 1)}


def similarity(a: str, b: str) -> float:
    """Jaccard 相似度（0~1）。"""
    sa, sb = shingles(a), shingles(b)
    if not sa or not sb:
        return 0.0
    return len(sa & sb) / len(sa | sb)


def open_db(path: Path) -> sqlite3.Connection:
    path.parent.mkdir(parents=True, exist_ok=True)
    conn = sqlite3.connect(str(path))
    conn.execute("PRAGMA journal_mode=WAL")
    # 中台可能有并发读者：无 busy_timeout 时偶发 "database is locked" 直接抛异常
    conn.execute("PRAGMA busy_timeout=5000")
    conn.execute("PRAGMA foreign_keys=ON")
    conn.executescript(
        """
        CREATE TABLE IF NOT EXISTS docs(
            id INTEGER PRIMARY KEY,
            path TEXT UNIQUE NOT NULL,
            kind TEXT NOT NULL,
            mtime REAL NOT NULL,
            size INTEGER NOT NULL
        );
        CREATE TABLE IF NOT EXISTS chunks(
            id INTEGER PRIMARY KEY,
            doc_id INTEGER NOT NULL REFERENCES docs(id) ON DELETE CASCADE,
            lineno INTEGER NOT NULL,
            text TEXT NOT NULL,
            seg TEXT NOT NULL
        );
        CREATE INDEX IF NOT EXISTS idx_chunks_doc ON chunks(doc_id);
        CREATE VIRTUAL TABLE IF NOT EXISTS chunks_fts USING fts5(
            seg, content='chunks', content_rowid='id', tokenize='unicode61'
        );
        CREATE TRIGGER IF NOT EXISTS chunks_ai AFTER INSERT ON chunks BEGIN
            INSERT INTO chunks_fts(rowid, seg) VALUES (new.id, new.seg);
        END;
        CREATE TRIGGER IF NOT EXISTS chunks_ad AFTER DELETE ON chunks BEGIN
            INSERT INTO chunks_fts(chunks_fts, rowid, seg) VALUES ('delete', old.id, old.seg);
        END;
        CREATE TRIGGER IF NOT EXISTS chunks_au AFTER UPDATE ON chunks BEGIN
            INSERT INTO chunks_fts(chunks_fts, rowid, seg) VALUES ('delete', old.id, old.seg);
            INSERT INTO chunks_fts(rowid, seg) VALUES (new.id, new.seg);
        END;
        """
    )
    return conn


def _root_rx(pattern: str) -> str:
    """把 SCAN_ROOTS 的通配模式转成正则（* 只匹配单层目录）。"""
    return "[^/]+".join(re.escape(part) for part in pattern.split("*"))


def _root_key(path: Path, home: Path) -> str:
    """判定某篇文档属于哪个具体扫描目录；认不出返回空串（视为可自由清理）。"""
    s = str(path)
    for pattern, _kind in SCAN_ROOTS:
        # 捕获组必须含 home 前缀：present 里存的是绝对路径，返回相对路径会永远匹配不上
        m = re.match("(" + re.escape(str(home)) + "/" + _root_rx(pattern) + ")/", s)
        if m:
            return m.group(1)
    if path.name in USER_MEMORY_FILES and path.parent.name.startswith("user-"):
        return str(path.parent)
    return ""


def collect_files(home: Path) -> tuple[list[tuple[Path, str]], set[str]]:
    """返回 (文件列表, 本次**可见的扫描目录集合**)。

    目录存在但被清空 = 正常删除（应清理旧文档）；目录整体不可见 = 掉线（必须保留旧索引）。
    两者只能靠「目录是否可见」区分，不能靠文件数——2026-11-23 实测就栽在这个区别上。
    """
    found: list[tuple[Path, str]] = []
    present: set[str] = set()
    for pattern, kind in SCAN_ROOTS:
        for base in sorted(home.glob(pattern)):
            if not base.is_dir():
                continue
            if any(part in SKIP_DIR_PARTS for part in base.parts):
                continue
            present.add(str(base))
            for path in sorted(base.rglob("*.md")):
                if any(part in SKIP_DIR_PARTS for part in path.parts):
                    continue
                found.append((path, kind))
    for path in sorted(home.glob(".workbuddy/user-*")):
        if not path.is_dir():
            continue
        present.add(str(path))
        for name in USER_MEMORY_FILES:
            candidate = path / name
            if candidate.is_file():
                found.append((candidate, "user-memory"))
    return found, present


def read_chunks(path: Path) -> list[tuple[int, str]] | None:
    """读取并切成 (行号, 文本) 片段；**读失败返回 None**，调用方必须当异常处理。

    2026-11-23 实测反例：读失败曾被当成「空文件」→ 建成 0 片段文档 + index 报成功
    + 查询静默「无命中」——与掉线清库同属静默丢失，只是规模更小。
    """
    try:
        raw = path.read_text(encoding="utf-8", errors="ignore")
    except OSError:
        return None
    raw = raw.lstrip("\ufeff")  # BOM 不进正文，避免出现在命中摘要里
    out = []
    for lineno, line in enumerate(raw.splitlines(), start=1):
        stripped = line.strip()
        if not stripped:
            continue
        if len(stripped) <= MAX_LINE_CHARS:
            out.append((lineno, stripped))
            continue
        # 长行切片：同一行号出多条 chunk，尾部内容不丢弃（2026-11-23 覆盖核验发现截断漏检）
        for start in range(0, len(stripped), MAX_LINE_CHARS):
            piece = stripped[start : start + MAX_LINE_CHARS]
            if piece:
                out.append((lineno, piece))
    return out


def run_index(db_path: Path, full: bool = False, home: Path | None = None) -> dict:
    """建/更新索引。返回统计。query 前会自动调用（增量 0.09s，避免读到过期快照）。

    🔴 掉线保护：若某扫描根本次命中 0 篇、而库中该根仍有文档，则判定该根「不可达」
    （外置卷未挂载 / 目录改名 / 权限失败），**保留旧索引并告警**，不把整库清空。
    2026-11-23 实测反例：外置卷掉线时旧实现删除全部文档、rc=0、查询静默返回「无命中」。
    """
    if full:
        # 只删主库会留下 -wal/-shm；崩溃残留的 wal 有可能把旧内容又接回来
        for suffix in ("", "-wal", "-shm"):
            candidate = Path(str(db_path) + suffix)
            if candidate.exists():
                candidate.unlink()
    conn = open_db(db_path)
    home = home or Path.home()
    files, present = collect_files(home)
    added = updated = unchanged = skipped = unreadable = 0
    total_bytes = 0
    started = time.time()
    for path, kind in files:
        try:
            stat = path.stat()
        except OSError:
            skipped += 1
            continue
        if stat.st_size > MAX_FILE_BYTES:
            skipped += 1
            continue
        total_bytes += stat.st_size
        key = str(path)
        row = conn.execute("SELECT id, mtime, size FROM docs WHERE path=?", (key,)).fetchone()
        if row and not full and abs(row[1] - stat.st_mtime) < 1 and row[2] == stat.st_size:
            unchanged += 1
            continue
        chunks = read_chunks(path)
        if chunks is None:
            # 🔴 读不到就跳过：绝不能当成空文件写库（旧文档保留原片段并下次重试）
            unreadable += 1
            continue
        if not chunks:
            # 空文件 / 只有空行：没有可检索内容，不建文档行（否则库里出现 0 片段文档）
            if row:
                conn.execute("DELETE FROM docs WHERE id=?", (row[0],))
                updated += 1
            else:
                skipped += 1
            continue
        if row:
            doc_id = row[0]
            conn.execute("UPDATE docs SET mtime=?, size=? WHERE id=?", (stat.st_mtime, stat.st_size, doc_id))
            conn.execute("DELETE FROM chunks WHERE doc_id=?", (doc_id,))
            updated += 1
        else:
            cur = conn.execute(
                "INSERT INTO docs(path, kind, mtime, size) VALUES (?,?,?,?)",
                (key, kind, stat.st_mtime, stat.st_size),
            )
            doc_id = cur.lastrowid
            added += 1
        conn.executemany(
            "INSERT INTO chunks(doc_id, lineno, text, seg) VALUES (?,?,?,?)",
            [(doc_id, lineno, text, seg(text)) for lineno, text in chunks],
        )
    conn.commit()
    live = {str(p) for p, _ in files}
    stale_by_root: dict[str, list[int]] = {}
    for doc_id, path_str in conn.execute("SELECT id, path FROM docs").fetchall():
        if path_str in live:
            continue
        rk = _root_key(Path(path_str), home)
        stale_by_root.setdefault(rk, []).append(doc_id)
    vanished = [rk for rk in stale_by_root if rk and rk not in present]
    kept = 0
    dropped = 0
    for rk, ids in stale_by_root.items():
        if rk in vanished:
            kept += len(ids)
            continue
        for doc_id in ids:
            conn.execute("DELETE FROM docs WHERE id=?", (doc_id,))
            dropped += 1
    if dropped:
        conn.commit()
    result = {
        "docs": conn.execute("SELECT count(*) FROM docs").fetchone()[0],
        "chunks": conn.execute("SELECT count(*) FROM chunks").fetchone()[0],
        "added": added,
        "updated": updated,
        "unchanged": unchanged,
        "skipped": skipped,
        "stale": dropped,
        "stale_kept": kept,
        "unreadable": unreadable,
        "vanished": vanished,
        "roots": sorted(present),
        "bytes": total_bytes,
        "seconds": time.time() - started,
    }
    conn.close()
    return result


def warn_vanished(r: dict) -> None:
    """把「索引不完整」打成显式告警——绝不允许表现为普通的「查询无命中」。"""
    vanished = r.get("vanished") or []
    if vanished:
        print(
            "[警告] 以下扫描目录本次不可见，库中旧索引已保留 → 本次结果可能过期: " + ", ".join(vanished),
            file=sys.stderr,
        )
        if r.get("stale_kept"):
            print(
                f"[警告] 共保留 {r['stale_kept']} 篇未清理。检查外置卷 ZHITAI 是否挂载、目录是否改名。",
                file=sys.stderr,
            )
    if r.get("unreadable"):
        print(
            f"[警告] {r['unreadable']} 篇文件读取失败（权限/损坏），已跳过且未覆盖库中旧内容 → "
            f"这些文件的内容本次查不到。",
            file=sys.stderr,
        )


def cmd_index(args: argparse.Namespace) -> int:
    db_path = Path(args.db).expanduser()
    r = run_index(db_path, full=args.full)
    print(
        f"索引完成: 文件 {r['docs']} 篇（新增 {r['added']} / 更新 {r['updated']} / 未变 {r['unchanged']} / "
        f"跳过 {r['skipped']} / 读不到 {r['unreadable']} / 清理 {r['stale']} / 保留 {r['stale_kept']}），"
        f"片段 {r['chunks']} 条，源 {r['bytes'] / 1024:.0f}KB，耗时 {r['seconds']:.1f}s"
    )
    print(f"库: {db_path}")
    warn_vanished(r)
    return 3 if (r["vanished"] or r["unreadable"]) else 0


def cmd_query(args: argparse.Namespace) -> int:
    query_text = " ".join(args.words)
    if args.limit < 1:
        # SQLite 的 LIMIT -1 意思是「不限制」，会一次吐出全库；必须挡在入口
        print(f"--limit 必须 ≥ 1（收到 {args.limit}）", file=sys.stderr)
        return 2
    db_path = Path(args.db).expanduser()
    if not db_path.exists():
        warn_vanished(run_index(db_path))
    elif not args.no_refresh:
        r = run_index(db_path, full=False)
        if r["added"] or r["updated"]:
            print(f"[索引已刷新: 新增 {r['added']} / 更新 {r['updated']}]", file=sys.stderr)
        warn_vanished(r)
    match = build_match(query_text)
    if not match:
        print(f"查询串为空或无可检索字符: {query_text!r}", file=sys.stderr)
        return 2
    conn = open_db(db_path)
    sql = """
        SELECT d.path, d.kind, c.lineno, c.text, bm25(chunks_fts) AS score
        FROM chunks_fts
        JOIN chunks c ON c.id = chunks_fts.rowid
        JOIN docs d ON d.id = c.doc_id
        WHERE chunks_fts MATCH ?
    """
    params: list[object] = [match]
    if args.kind:
        sql += " AND d.kind = ?"
        params.append(args.kind)
    if args.path_like:
        sql += " AND d.path LIKE ?"
        params.append(f"%{args.path_like}%")
    sql += " ORDER BY score LIMIT ?"
    params.append(args.limit)
    try:
        rows = conn.execute(sql, params).fetchall()
    except sqlite3.OperationalError as exc:
        print(f"查询失败: {exc}", file=sys.stderr)
        conn.close()
        return 2
    conn.close()
    if args.json:
        print(json.dumps(
            [{"path": r[0], "kind": r[1], "line": r[2], "text": r[3], "score": round(r[4], 4)} for r in rows],
            ensure_ascii=False, indent=2,
        ))
        return 0
    if not rows:
        print(f"无命中: {query_text}")
        return 1
    print(f"命中 {len(rows)} 条（MATCH: {match}）")
    for path, kind, lineno, text, score in rows:
        short = text if len(text) <= args.width else text[: args.width] + "…"
        print(f"\n[{kind}] {Path(path).name}:{lineno}  ({score:.2f})")
        print(f"  {short}")
        print(f"  {path}")
    return 0


def cmd_similar(args: argparse.Namespace) -> int:
    """写新经验前查重：草稿 vs 库中已有文档的字符 3-gram Jaccard 相似度。"""
    if args.file == "-":
        draft = sys.stdin.read()
    else:
        draft_path = Path(args.file).expanduser()
        if not draft_path.is_file():
            print(f"草稿不存在: {draft_path}", file=sys.stderr)
            return 2
        draft = draft_path.read_text(encoding="utf-8", errors="ignore")
    if not draft.strip():
        print("草稿为空，无法查重", file=sys.stderr)
        return 2
    db_path = Path(args.db).expanduser()
    if not db_path.exists():
        warn_vanished(run_index(db_path))
    elif not args.no_refresh:
        warn_vanished(run_index(db_path, full=False))
    seeds = extract_seeds(draft, args.seeds * 2)
    match = build_match_any(seeds)
    if not match:
        print("草稿里没有可检索的词，无法查重", file=sys.stderr)
        return 2
    conn = open_db(db_path)
    total_docs = conn.execute("SELECT count(*) FROM docs").fetchone()[0] or 1

    def df(cut: str) -> int:
        return conn.execute(
            "SELECT count(DISTINCT c.doc_id) FROM chunks_fts JOIN chunks c ON c.id=chunks_fts.rowid "
            "WHERE chunks_fts MATCH ?",
            ('"' + cut + '"',),
        ).fetchone()[0]

    # 种子按稀有度排序：词频最高的往往是最没区分度的（文档/索引/命中），
    # 全靠它们选候选只会选出长文件（实测草稿原文自己都进不了候选）。
    scored = [(df(cut), term, cut) for term in seeds if (cut := seg(term))]
    rare = [s for s in scored if s[0] <= max(3, int(total_docs * 0.25))] or sorted(scored)[:3]
    rare.sort(key=lambda s: (s[0], s[1]))
    seeds = [term for _d, term, _c in rare[: args.seeds]]
    if not seeds:
        print("草稿里没有足够有区分度的词，无法查重", file=sys.stderr)
        conn.close()
        return 2

    # 候选：每个种子取命中行数最多的 200 篇，再按「命中几个种子」排序。
    # 必须带 ORDER BY：无排序 + LIMIT 会按 doc_id 截断，新文档直接落到窗口外（实测 doc 998 被漏）。
    coverage: dict[int, int] = {}
    meta: dict[int, tuple[str, str]] = {}
    for term in seeds:
        cut = seg(term)
        for doc_id, path, kind, _hits in conn.execute(
            """SELECT d.id, d.path, d.kind, count(c.id) AS hits FROM chunks_fts
               JOIN chunks c ON c.id = chunks_fts.rowid JOIN docs d ON d.id = c.doc_id
               WHERE chunks_fts MATCH ? GROUP BY d.id ORDER BY hits DESC LIMIT 200""",
            ('"' + cut + '"',),
        ).fetchall():
            coverage[doc_id] = coverage.get(doc_id, 0) + 1
            meta[doc_id] = (path, kind)
    ranked = sorted(coverage.items(), key=lambda kv: (-kv[1], kv[0]))[: args.candidates]
    rows = []
    for doc_id, hits in ranked:
        body = "\n".join(
            t for (t,) in conn.execute("SELECT text FROM chunks WHERE doc_id=? ORDER BY lineno", (doc_id,))
        )
        path, kind = meta[doc_id]
        rows.append((similarity(draft, body), path, kind, hits))
    conn.close()
    rows.sort(key=lambda r: (-r[0], r[1]))
    if not rows:
        print("未发现任何候选历史记录 → 可新建。")
        return 0
    n = len(seeds)
    top_ratio = rows[0][0]
    top_cover = max(r[3] / n for r in rows)
    cover_row = max(rows, key=lambda r: r[3])
    print(f"草稿 {len(draft)} 字，{n} 个稀有字符片段种子（{', '.join(seeds[:6])}），候选 {len(rows)} 篇：")
    for ratio, path, kind, hits in rows[: args.limit]:
        cover = hits / n
        flag = ""
        if ratio >= args.threshold:
            flag = "  ← 疑似副本/改写"
        elif cover >= args.cover:
            flag = "  ← 主题可能已覆盖"
        print(f"\n[{kind}] 文本相似度 {ratio:.2f} ｜ 种子覆盖 {hits}/{n}（{cover:.0%}）{flag}")
        print(f"  {path}")
    reasons = []
    if top_ratio >= args.threshold:
        reasons.append(f"文本相似度 {top_ratio:.2f} ≥ {args.threshold:.2f}，疑似副本/改写")
    if top_cover >= args.cover:
        reasons.append(f"种子覆盖 {top_cover:.0%} ≥ {args.cover:.0%}，同主题可能已写过")
    if reasons:
        print("\n判定: 先读上面的候选再决定 —— " + "；".join(reasons))
        print(f"  最相关: {cover_row[1]}")
        return 4
    print(f"\n判定: 未达重复阈值，可新建（最高文本相似度 {top_ratio:.2f}，最高种子覆盖 {top_cover:.0%}）")
    return 0


def cmd_stats(args: argparse.Namespace) -> int:
    db_path = Path(args.db).expanduser()
    if not db_path.exists():
        print("索引库不存在", file=sys.stderr)
        return 2
    conn = open_db(db_path)
    print(f"库: {db_path}  ({db_path.stat().st_size / 1024:.0f}KB)")
    for kind, docs, chunks in conn.execute(
        """SELECT d.kind, count(DISTINCT d.id), count(c.id)
           FROM docs d LEFT JOIN chunks c ON c.doc_id = d.id GROUP BY d.kind ORDER BY 2 DESC"""
    ):
        print(f"  {kind:<12} 文件 {docs:<5} 片段 {chunks}")
    newest = conn.execute("SELECT path, mtime FROM docs ORDER BY mtime DESC LIMIT 1").fetchone()
    if newest:
        print(f"  最新: {newest[0]}  ({time.strftime('%Y-%m-%d %H:%M', time.localtime(newest[1]))})")
    conn.close()
    return 0


def cmd_self_test(args: argparse.Namespace) -> int:
    checks: list[tuple[str, bool, str]] = []

    def check(name: str, cond: bool, detail: str = "") -> None:
        checks.append((name, bool(cond), detail))

    check("seg 中文逐字", seg("止损") == "止 损", seg("止损"))
    check("seg 中英混排", seg("FTS5 索引") == "fts5 索 引", seg("FTS5 索引"))
    check("match 单词 phrase", build_match("止损") == '"止 损"', build_match("止损"))
    check("match 多词 AND", build_match("止损 仓位") == '"止 损" AND "仓 位"', build_match("止损 仓位"))
    check("match 空串", build_match("   ") == "", repr(build_match("   ")))

    tmp = Path("/tmp/mem-search-selftest.db")
    if tmp.exists():
        tmp.unlink()
    conn = open_db(tmp)
    doc = conn.execute(
        "INSERT INTO docs(path, kind, mtime, size) VALUES ('/x/a.md','learnings',?,-1)", (time.time(),)
    )
    doc_id = doc.lastrowid
    samples = [
        (1, "止损规则：主板 -8%，创业板 -15%"),
        (2, "半导体仓位上限 50%，当前 77% 超限"),
        (3, "TCC EPERM：后台任务读外置卷失败"),
        (4, "pre-commit hook 缺失导致 CI 红（v1.2.0 起）"),
    ]
    conn.executemany(
        "INSERT INTO chunks(doc_id, lineno, text, seg) VALUES (?,?,?,?)",
        [(doc_id, ln, tx, seg(tx)) for ln, tx in samples],
    )
    conn.commit()

    def hit(q: str) -> list[int]:
        rows = conn.execute(
            """SELECT c.lineno FROM chunks_fts JOIN chunks c ON c.id=chunks_fts.rowid
               WHERE chunks_fts MATCH ?""", (build_match(q),),
        ).fetchall()
        return sorted(r[0] for r in rows)

    check("2 字词命中（trigram 做不到）", hit("止损") == [1], str(hit("止损")))
    check("3 字以上词命中", hit("创业板") == [1], str(hit("创业板")))
    check("多词 AND 收窄", hit("仓位 上限") == [2], str(hit("仓位 上限")))
    check("跨词不误命中", hit("止损 仓位") == [], str(hit("止损 仓位")))
    check("英文缩略词命中", hit("EPERM") == [3], str(hit("EPERM")))
    # 回归（2026-11-23）：查询串含连字符/点曾被 ALLOWED_RE 整条拒掉，导致 pre-commit 类查询静默失败
    check("连字符查询不被拒", build_match("pre-commit") == '"pre commit"', build_match("pre-commit"))
    check("连字符查询能命中", hit("pre-commit") == [4], str(hit("pre-commit")))
    check("连字符 + 中文", hit("pre-commit 缺失") == [4], str(hit("pre-commit 缺失")))
    check("带点版本号能命中", hit("v1.2.0") == [4], str(hit("v1.2.0")))
    check("任务号形态可清洗", build_match("T-INS-abc123") == '"t ins abc123"', build_match("T-INS-abc123"))
    check("无命中返回空", hit("不存在的词") == [], str(hit("不存在的词")))

    conn.execute("DELETE FROM docs WHERE id=?", (doc_id,))
    conn.commit()
    left = conn.execute("SELECT count(*) FROM chunks").fetchone()[0]
    check("删文档级联清片段", left == 0, f"残留 {left}")
    ftx = conn.execute("SELECT count(*) FROM chunks_fts").fetchone()[0]
    check("FTS 触发器同步", ftx == 0, f"FTS 残留 {ftx}")
    conn.close()
    tmp.unlink(missing_ok=True)

    # 回归：长行必须切片而非截断（2026-11-23 覆盖核验实测 3116 字符行「超时」落在 2042 位被丢）
    import tempfile
    with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False, encoding="utf-8") as fh:
        fh.write("短行止损\n" + "填" * 2100 + "超时\n")
        long_path = Path(fh.name)
    pieces = read_chunks(long_path)
    long_path.unlink(missing_ok=True)
    check("长行切片不丢弃", len(pieces) == 3, f"实际 {len(pieces)} 条")
    check("长行尾部内容保留", any("超时" in text for _, text in pieces), "尾部词丢失")

    # ---- 读文件边界（2026-11-23 实测：读失败曾被当空文件，建出 0 片段文档 → 检索永远查不到）----
    check("读失败返回 None 而非空列表", read_chunks(Path("/nonexistent/xx.md")) is None,
          str(read_chunks(Path("/nonexistent/xx.md"))))
    with tempfile.NamedTemporaryFile("w", suffix=".md", delete=False, encoding="utf-8") as fh:
        fh.write("")
        empty_path = Path(fh.name)
    check("空文件返回空片段", read_chunks(empty_path) == [], str(read_chunks(empty_path)))
    with tempfile.NamedTemporaryFile("wb", suffix=".md", delete=False) as fh:
        fh.write("\ufeff# 带 BOM 的标题\n正文止损\n".encode())
        bom_path = Path(fh.name)
    bom_chunks = read_chunks(bom_path)
    check("BOM 不进正文", bool(bom_chunks) and bom_chunks[0][1].startswith("#"), str(bom_chunks[:1]))
    for p in (empty_path, bom_path):
        p.unlink(missing_ok=True)

    # ---- 查重（similar）纯函数 ----
    check("相似度自反", similarity("止损与仓位上限", "止损与仓位上限") > 0.99, f"{similarity('a止损','a止损'):.2f}")
    check("相似度无关", similarity("止损规则与仓位", "飞书机器人卡片推送") < 0.2,
          f"{similarity('止损规则与仓位', '飞书机器人卡片推送'):.2f}")
    check("空文本相似度为 0", similarity("", "非空内容") == 0.0)
    seeds = extract_seeds("pre-commit hook 缺失导致 CI 红，pre-commit 要装")
    check("种子含英文词", "pre" in seeds or "commit" in seeds, str(seeds[:5]))
    check("种子含中文多字组", any(len(s) >= 2 and not s.isascii() for s in seeds), str(seeds[:5]))
    # 文档命令闸门自身的可证伪性：合法命令 0 问题，伪造子命令/选项各报 1 条
    bad_probe = _validate_calls(["index", "query --limit 5", "self-tst", "stats --nope"])
    check("文档命令闸门能识别伪造项", len(bad_probe) == 2, str(bad_probe))

    # ---- 掉线保护（2026-11-23 复现：外置卷掉线时旧实现清空整库、rc=0、查询静默「无命中」）----
    import shutil
    import tempfile

    fake_home = Path(tempfile.mkdtemp(prefix="memsearch-home-"))
    fake_dbd = Path(tempfile.mkdtemp(prefix="memsearch-dbd-"))
    wipe_db = fake_dbd / "w.db"
    try:
        (fake_home / "WorkBuddy/Claw/.learnings").mkdir(parents=True)
        (fake_home / "WorkBuddy/QTS/.learnings").mkdir(parents=True)
        (fake_home / "WorkBuddy/Claw/.learnings/a.md").write_text("# 止损\n主板 -8%\n", encoding="utf-8")
        (fake_home / "WorkBuddy/QTS/.learnings/b.md").write_text("# 幂等\n事件 id 去重\n", encoding="utf-8")
        (fake_home / "WorkBuddy/QTS/.learnings/empty.md").write_text("", encoding="utf-8")
        r1 = run_index(wipe_db, full=True, home=fake_home)
        check("掉线保护·基线索引", r1["docs"] == 2 and not r1["vanished"], f"docs={r1['docs']} van={r1['vanished']}")
        conn0 = open_db(wipe_db)
        empties = conn0.execute(
            "SELECT count(*) FROM docs d WHERE NOT EXISTS (SELECT 1 FROM chunks c WHERE c.doc_id=d.id)"
        ).fetchone()[0]
        conn0.close()
        check("空文件不建 0 片段文档", empties == 0, f"0 片段文档 {empties} 篇")

        (fake_home / "WorkBuddy/Claw/.learnings/a.md").unlink()
        r2 = run_index(wipe_db, home=fake_home)
        check("目录健在·文件删除仍清理", r2["docs"] == 1 and r2["stale"] == 1,
              f"docs={r2['docs']} stale={r2['stale']}")
        check("目录健在·不误报掉线", r2["vanished"] == [], str(r2["vanished"]))

        (fake_home / "WorkBuddy").rename(fake_home / "WorkBuddy-away")
        r3 = run_index(wipe_db, home=fake_home)
        check("目录消失·不清库", r3["docs"] == 1, f"docs={r3['docs']}")
        check("目录消失·被识别", len(r3["vanished"]) == 1, str(r3["vanished"]))
        check("目录消失·保留计数", r3["stale_kept"] == 1 and r3["stale"] == 0,
              f"kept={r3['stale_kept']} dropped={r3['stale']}")
        (fake_home / "WorkBuddy-away").rename(fake_home / "WorkBuddy")

        # 查重端到端：草稿与已索引文档近乎同文，应能经种子召回并算出高相似度
        draft = "# 幂等\n事件 id 去重\n"
        conn2 = open_db(wipe_db)
        got = conn2.execute(
            """SELECT d.path, group_concat(c.text, char(10)) FROM chunks_fts
               JOIN chunks c ON c.id=chunks_fts.rowid JOIN docs d ON d.id=c.doc_id
               WHERE chunks_fts MATCH ? GROUP BY d.id""",
            (build_match_any(extract_seeds(draft)),),
        ).fetchall()
        conn2.close()
        check("查重·种子能召回同文文档", any("b.md" in r[0] for r in got), str([r[0] for r in got]))
        best = max((similarity(draft, r[1]) for r in got), default=0.0)
        check("查重·同文相似度达阈值", best >= 0.9, f"{best:.2f}")
    finally:
        shutil.rmtree(fake_home, ignore_errors=True)
        shutil.rmtree(fake_dbd, ignore_errors=True)

    passed = sum(1 for _, ok, _ in checks if ok)
    for name, ok, detail in checks:
        print(f"{'PASS' if ok else 'FAIL'}  {name}" + (f"  [{detail}]" if not ok and detail else ""))
    print(f"\n{passed}/{len(checks)} 通过")
    return 0 if passed == len(checks) else 1


def _validate_calls(calls: list[str]) -> list[str]:
    """核对每条命令的子命令与选项是否真实存在；返回问题清单（空 = 全部存在）。"""
    subs, flags = _parser_surface()
    problems: list[str] = []
    for call in calls:
        head = next((t for t in call.split() if not t.startswith("-") and t != "|"), "")
        if head and head not in subs:
            problems.append(f"子命令 {head}（{call}）")
        for tok in call.split():
            if tok.startswith("--"):
                name = tok.split("=", 1)[0]
                if name not in flags:
                    problems.append(f"选项 {name}（{call}）")
    return problems


def _looks_like_call(tail: str) -> bool:
    """只有「首词是 ASCII 子命令名」才当命令行；否则是散文（如 docstring 首行的「—— 本地…」）。"""
    return bool(re.match(r"^[a-z][a-z0-9-]*(\s|$)", tail))


def _docstring_calls() -> list[str]:
    """脚本自身 docstring 里列出的命令（最初那个 --self-test 错误就出在这里）。"""
    calls = []
    for line in (__doc__ or "").splitlines():
        stripped = line.strip()
        if stripped.startswith("mem-search.py"):
            tail = stripped.split("mem-search.py", 1)[1].split("#", 1)[0].strip()
            if tail and _looks_like_call(tail):
                calls.append(tail)
    return calls


def _repo_root_of(path: Path) -> Path | None:
    """返回文件所在 git 仓根；不在仓内返回 None。"""
    proc = subprocess.run(
        ["git", "-C", str(path.parent), "rev-parse", "--show-toplevel"],
        capture_output=True, text=True,
    )
    if proc.returncode != 0:
        return None
    return Path(proc.stdout.strip())


def _hook_gate_status(root: Path | None) -> tuple[bool, str]:
    """自动闸门是否真的挂着。闸门自己丢了也是「静默失效」，必须可断言。"""
    if root is None:
        return False, "真源不在 git 仓，无法定位钩子"
    hook = root / ".git" / "hooks" / "pre-commit"
    if not hook.is_file():
        return False, f"钩子不存在: {hook}"
    if not os.access(hook, os.X_OK):
        return False, f"钩子无执行权限: {hook}"
    body = hook.read_text(encoding="utf-8", errors="ignore")
    if "mem-search" not in body or "verify" not in body:
        return False, "钩子存在但未调用 mem-search verify"
    return True, "pre-commit → mem-search verify"


def _offsite_status(root: Path | None) -> tuple[bool, str]:
    """异地副本是否同步。判据只用本地 refs（不联网），离线也能跑。

    取「HEAD vs 本地缓存的 origin/main」：一致即已推送。缓存过期的极端情况
    只会让这一项 ERROR 到 WARN，不会把「从未推送」误判成已备份。
    """
    if root is None:
        return False, "真源不在 git 仓，无法比对远端"
    url = subprocess.run(
        ["git", "-C", str(root), "remote", "get-url", "origin"],
        capture_output=True, text=True,
    )
    if url.returncode != 0:
        return False, "无 origin 远端（异地副本不存在，磁盘故障即全丢）"
    head = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "HEAD"], capture_output=True, text=True,
    ).stdout.strip()
    remote = subprocess.run(
        ["git", "-C", str(root), "rev-parse", "refs/remotes/origin/main"],
        capture_output=True, text=True,
    )
    rsha = remote.stdout.strip()
    if remote.returncode != 0 or not rsha:
        return False, "远端分支未建立（从未推送过）"
    if head != rsha:
        ahead = subprocess.run(
            ["git", "-C", str(root), "rev-list", "--count", f"{rsha}..HEAD"],
            capture_output=True, text=True,
        ).stdout.strip()
        return False, f"本地领先 {ahead or '?'} 个提交未推送"
    return True, f"origin/main = {head[:7]}"


def _sample_self_match(conn: sqlite3.Connection, n: int = 194, seed: int = 20261123) -> dict:
    """抽样自匹配：随机取 n 个片段，用它自己最稀有的连续二元组查**全部**命中（不截断），
    核对自身是否出现。测的是「每一行都真的可检索」，而不是「表里有这些行」。

    为什么要这么做：`--limit` 截断后的结果集不能用来判覆盖（曾据此假报 65 篇漏索引）；
    而只数 `count(*)` 又看不出内容是否切错。命中集过大的样本直接跳过，不做近似判断。
    """
    rng = random.Random(seed)
    rows = conn.execute(
        "SELECT c.lineno, c.text, d.path FROM chunks c JOIN docs d ON d.id = c.doc_id"
    ).fetchall()
    pool = list(rows)
    rng.shuffle(pool)
    checked = 0
    miss: list[str] = []
    for lineno, text, path in pool:
        if checked >= n:
            break
        toks = seg(text).split()
        if len(toks) < 4:
            continue
        best = None  # (df, phrase)：挑最稀有窗口，命中集才够小，「不在结果里」才有意义
        for start in rng.sample(range(len(toks) - 1), min(4, len(toks) - 1)):
            phrase = '"' + " ".join(toks[start:start + 2]) + '"'
            df = conn.execute(
                "SELECT count(*) FROM chunks_fts WHERE chunks_fts MATCH ?", (phrase,)
            ).fetchone()[0]
            if df and (best is None or df < best[0]):
                best = (df, phrase)
        if best is None:
            continue
        got = conn.execute(
            "SELECT d.path, c.lineno FROM chunks_fts JOIN chunks c ON c.id = chunks_fts.rowid "
            "JOIN docs d ON d.id = c.doc_id WHERE chunks_fts MATCH ? LIMIT 5000",
            (best[1],),
        ).fetchall()
        if len(got) >= 5000:
            continue
        checked += 1
        if (path, lineno) not in set(got):
            miss.append(f"{path}:{lineno}")
    return {"checked": checked, "miss": miss}


def _source_match(conn: sqlite3.Connection) -> dict:
    """源文件与索引逐段比对：每篇文档重新解析一次，与库内 (lineno, text) 序列必须完全一致。

    为什么不是「数片段数」：那样枚举的是**库内已有行**，一行 2 片被删成 1 片后
    该行直接从候选集消失，闸门照样绿（本轮实测踩到）。这里枚举源文件，才看得见“少了”。
    源文件比索引新（未刷新）时跳过，避免把「还没增量刷新」误报成丢数据。
    """
    docs = conn.execute("SELECT id, path, mtime FROM docs ORDER BY id").fetchall()
    bad: list[str] = []
    skipped = 0
    for doc_id, path, mtime in docs:
        p = Path(path)
        try:
            if p.stat().st_mtime > (mtime or 0) + 1:
                skipped += 1
                continue
            fresh = read_chunks(p)
        except OSError:
            skipped += 1
            continue
        if fresh is None:
            skipped += 1
            continue
        in_db = conn.execute(
            "SELECT lineno, text FROM chunks WHERE doc_id=? ORDER BY id", (doc_id,)
        ).fetchall()
        if [tuple(r) for r in in_db] != fresh:
            bad.append(f"{path} 源 {len(fresh)} 段/库 {len(in_db)} 段")
    return {"docs": len(docs) - skipped, "bad": bad, "skipped": skipped}


def cmd_verify(args: argparse.Namespace) -> int:
    """交付前总闸：把「做完了」从主观判断改成七项可执行判据。"""
    # (名称, 通过, 详情, 仅告警) —— 仅告警项失败不算交付失败，但要显式打印
    results: list[tuple[str, bool, str, bool]] = []

    # 1) 自检（含分词/截断/掉线保护/查重端到端）
    proc = subprocess.run(
        [sys.executable, str(Path(__file__).resolve()), "self-test"],
        capture_output=True, text=True,
    )
    tail = (proc.stdout.strip().splitlines() or ["(无输出)"])[-1]
    results.append(("self-test 全绿", proc.returncode == 0, tail, False))

    # 2) 文档命令 vs 实现：SKILL.md 里写的子命令与选项必须真实存在
    skill = Path(args.skill).expanduser()
    if not skill.is_file():
        results.append(("文档命令可执行", False, f"技能文件不存在: {skill}", False))
    else:
        calls = _documented_calls(skill)
        bad = _validate_calls(calls)
        results.append((f"技能文档命令可执行（{len(calls)} 条）", bool(calls) and not bad,
                        "; ".join(bad[:4]) or ("全部存在" if calls else "未解析到任何命令"), False))

    doc_calls = _docstring_calls()
    doc_bad = _validate_calls(doc_calls)
    results.append((f"脚本自带命令可执行（{len(doc_calls)} 条）", bool(doc_calls) and not doc_bad,
                    "; ".join(doc_bad[:4]) or ("全部存在" if doc_calls else "未解析到命令"), False))

    # 3) 索引健康：非空 + 无 0 片段文档 + 抽样自匹配 + 长行切片完整
    #    0 片段 = 内容对检索不可见；自匹配 = 每行真能查回来；切片 = 长行尾部没被截掉
    db = Path(args.db).expanduser()
    if not db.exists():
        results.append(("索引健康", False, "索引库不存在，先跑 index", False))
    else:
        conn = open_db(db)
        docs = conn.execute("SELECT count(*) FROM docs").fetchone()[0]
        empty = conn.execute(
            "SELECT count(*) FROM docs d WHERE NOT EXISTS (SELECT 1 FROM chunks c WHERE c.doc_id = d.id)"
        ).fetchone()[0]
        cover = _sample_self_match(conn)
        sl = _source_match(conn)
        conn.close()
        n_ck, n_miss = cover["checked"], cover["miss"]
        # 跳过率过高 = 源库比对基本没生效，此时「不符 0」是假绿，必须报红而不是放行
        skip_ratio = sl["skipped"] / docs if docs else 0.0
        ok = (docs > 0 and empty == 0 and n_ck > 0 and not n_miss
              and not sl["bad"] and skip_ratio <= 0.05)
        detail = (
            f"文档 {docs} 篇，0 片段 {empty} 篇，"
            f"抽样自匹配 {n_ck - len(n_miss)}/{n_ck}，"
            f"源库一致 {sl['docs']}/{docs}（不符 {len(sl['bad'])}）"
        )
        if sl["skipped"]:
            detail += f"（跳 {sl['skipped']} 篇源已更新）"
        if skip_ratio > 0.05:
            detail += "；跳过率 >5%，源库比对基本没生效，先 index 再验"
        if n_miss:
            detail += "；漏检 " + "，".join(n_miss[:3])
        if not n_ck:
            detail += "；抽样为空，覆盖未验证"
        if sl["bad"]:
            detail += "；不一致 " + "，".join(sl["bad"][:2])
        results.append(("索引健康（非空+可检索+源库一致）", ok, detail, False))

    # 4) 真源受版本控制：索引库可重建，脚本不可重建（902 行唯一副本 = 单点故障）
    src = Path(__file__).resolve()
    root = _repo_root_of(src)
    if root is None:
        results.append(("真源受版本控制", False, f"{src} 不在任何 git 仓", False))
    else:
        rel = src.relative_to(root)
        ls = subprocess.run(
            ["git", "-C", str(root), "ls-files", "--error-unmatch", str(rel)],
            capture_output=True, text=True,
        )
        results.append((
            "真源受版本控制",
            ls.returncode == 0,
            f"{rel} @ {root.name}" if ls.returncode == 0 else f"{rel} 未被 git 跟踪",
            False,
        ))

    # 5) 自动闸门在位：否则「verify 要记得跑」等于没有闸门
    hook_ok, hook_detail = _hook_gate_status(root)
    results.append(("自动闸门在位", hook_ok, hook_detail, False))

    # 6) 异地副本：真源仓与技能文档仓可能不是同一个仓（2026-11-23 实测：确为两仓），都要断言
    targets: list[tuple[str, Path | None]] = [("真源", root)]
    skill_root = _repo_root_of(skill) if skill.is_file() else None
    if skill_root is not None and skill_root != root:
        targets.append(("技能", skill_root))
    parts: list[str] = []
    off_ok = True
    for label, troot in targets:
        ok, detail = _offsite_status(troot)
        parts.append(f"{label} {detail}")
        off_ok = off_ok and ok
    if skill_root is None:
        # 定位不到仓 ≠ 这一边没问题：可能是文档不在 git 仓，也可能是 git 探不到（如 TCC EPERM）。
        # 两种情况下技能仓都没被验证，不能报绿——否则就是「覆盖不了仍亮绿灯」的静默漏检。
        parts.append("技能文档所在仓无法定位（不在 git 仓或 git 不可用），该边未验证")
        off_ok = False
    results.append(("异地副本已同步", off_ok, "；".join(parts), True))

    passed = sum(1 for _, ok, _, _ in results if ok)
    warned = 0
    for name, ok, detail, warn_only in results:
        if ok:
            tag = "PASS"
        elif warn_only:
            tag = "WARN"
            warned += 1
        else:
            tag = "FAIL"
        print(f"{tag}  {name}" + (f"  [{detail}]" if detail else ""))
    failed = len(results) - passed - warned
    if getattr(args, "strict", False):
        failed += warned
    tail = f"\n{passed}/{len(results)} 通过"
    if warned:
        tail += f"，{warned} 项告警（不阻断本地提交，但交付前应清零）"
    print(tail)
    return 0 if failed == 0 else 1


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(description="本地 Markdown 经验资产全文检索（FTS5 单字切分）")
    parser.add_argument("--db", default=os.environ.get("MEM_SEARCH_DB", str(DB_PATH)))
    sub = parser.add_subparsers(dest="cmd", required=True)

    p_index = sub.add_parser("index", help="建立/更新索引")
    p_index.add_argument("--full", action="store_true", help="删除并全量重建")
    p_index.set_defaults(func=cmd_index)

    p_query = sub.add_parser("query", help="检索")
    p_query.add_argument("words", nargs="+", help="查询词，空格分隔表示 AND")
    p_query.add_argument("--limit", type=int, default=10)
    p_query.add_argument("--kind", choices=["learnings", "memory", "user-memory"], default=None)
    p_query.add_argument("--path-like", dest="path_like", default=None, help="按路径子串过滤")
    p_query.add_argument("--width", type=int, default=200, help="摘要宽度")
    p_query.add_argument("--json", action="store_true")
    p_query.add_argument("--no-refresh", dest="no_refresh", action="store_true", help="跳过查询前的增量刷新")
    p_query.set_defaults(func=cmd_query)

    sub.add_parser("stats", help="索引统计").set_defaults(func=cmd_stats)

    p_similar = sub.add_parser("similar", help="写新经验前查重：草稿 vs 库中历史")
    p_similar.add_argument("file", help="草稿文件路径，- 表示从 stdin 读")
    p_similar.add_argument("--limit", type=int, default=5)
    p_similar.add_argument("--candidates", type=int, default=30, help="参与相似度计算的候选篇数")
    p_similar.add_argument("--seeds", type=int, default=10, help="取几个检索种子")
    p_similar.add_argument("--threshold", type=float, default=0.30, help="文本相似度阈值（判副本/改写）")
    p_similar.add_argument("--cover", type=float, default=0.60, help="稀有种子覆盖率阈值（判同主题已写过）")
    p_similar.add_argument("--no-refresh", dest="no_refresh", action="store_true")
    p_similar.set_defaults(func=cmd_similar)

    sub.add_parser("self-test", help="自检").set_defaults(func=cmd_self_test)

    p_verify = sub.add_parser("verify", help="交付前总闸：自检 + 文档一致性 + 索引健康 + 异地副本")
    p_verify.add_argument("--skill", default=str(SKILL_PATH), help="技能文档路径（用于核对文档命令）")
    p_verify.add_argument("--strict", action="store_true", help="告警项也视为失败（交付前用）")
    p_verify.set_defaults(func=cmd_verify)

    return parser


def _documented_calls(skill_path: Path) -> list[str]:
    """抽出 SKILL.md 的 bash 代码块中所有 mem-search.py 调用（只取脚本名之后的部分）。"""
    try:
        text = skill_path.read_text(encoding="utf-8", errors="ignore")
    except OSError:
        return []
    calls: list[str] = []
    in_block = False
    for line in text.splitlines():
        stripped = line.strip()
        if stripped.startswith("```"):
            in_block = not in_block
            continue
        if in_block and "mem-search.py" in stripped:
            tail = stripped.split("mem-search.py", 1)[1].strip()
            tail = tail.split("#", 1)[0].strip()  # 去掉行尾注释
            if tail and _looks_like_call(tail):
                calls.append(tail)
    return calls


def _parser_surface() -> tuple[set[str], set[str]]:
    """返回 (子命令集合, 可接受选项集合)，用于反证文档里写的命令是否真实存在。"""
    parser = build_parser()
    subs: set[str] = set()
    flags: set[str] = set()
    for action in parser._actions:
        flags.update(action.option_strings)
        if isinstance(action, argparse._SubParsersAction):
            for name, sub_parser in action.choices.items():
                subs.add(name)
                for sub_action in sub_parser._actions:
                    flags.update(sub_action.option_strings)
    return subs, flags


def main(argv: list[str] | None = None) -> int:
    parser = build_parser()
    args = parser.parse_args(argv)
    try:
        return args.func(args)
    except sqlite3.DatabaseError as exc:
        print(
            f"索引库不可用（可能是损坏或非 SQLite 文件）: {exc}\n"
            f"库: {args.db}\n修复: 删除后重建 —— rm -f {args.db} && {Path(__file__).name} --db {args.db} index",
            file=sys.stderr,
        )
        return 2


if __name__ == "__main__":
    sys.exit(main())
