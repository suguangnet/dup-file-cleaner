# -*- coding: utf-8 -*-
"""重复文件及目录查找清理工具

流程：扫描 -> 列出重复组（每组保留时间最早的一份，其余标记删除）-> 用户确认 -> 删除
"""
import csv
import ctypes
import hashlib
import heapq
import json
import os
import queue
import shutil
import stat
import sys
import threading
import time
import tkinter as tk
from ctypes import wintypes
from tkinter import filedialog, messagebox, ttk

APP_TITLE = "重复文件及目录清理工具"
FOOTER_TEXT = "速光网络软件开发  suguang.cc    抖音：dubaishun12"

SKIP_DIRS = {"$recycle.bin", "system volume information", "$windows.~bt",
             "$windows.~ws", "windowsapps", "recovery", "config.msi"}
# 代码项目保护：依赖/缓存目录不遍历；含标志文件的目录视为项目根，项目内部不做文件级和子目录级去重
DEFAULT_DEP_DIRS = ("node_modules, bower_components, vendor, venv, .venv, site-packages, __pycache__, "
                    ".next, .nuxt, .gradle, .tox, .mypy_cache, .pytest_cache, .idea, .vs")
# 程序目录（代码项目、网站、App、软件/游戏、数据库、服务部署）的标志；程序目录内部不做单文件去重
PROJECT_MARKERS = {
    # 代码项目
    "package.json", "composer.json", "requirements.txt", "pyproject.toml", "setup.py", "pipfile",
    "pom.xml", "build.gradle", "build.gradle.kts", "settings.gradle", "go.mod", "cargo.toml", "gemfile",
    "artisan", "cmakelists.txt", "makefile", "pubspec.yaml", "androidmanifest.xml", "pages.json",
    "project.config.json", "tsconfig.json", "vite.config.js", "vite.config.ts", "webpack.config.js",
    ".git", ".svn", ".gitignore",
    # 网站
    "index.php", "index.html", "index.htm", "index.jsp", "default.aspx", ".htaccess", "web.config",
    "wp-config.php",
    # 数据库
    "ibdata1", "auto.cnf", "my.ini", "my.cnf",
    # 服务部署 / 浏览器配置 / 光盘软件
    "dockerfile", "docker-compose.yml", "nginx.conf", "local state", "preferences", "autorun.inf",
}
PROJECT_MARKER_EXTS = (".sln", ".csproj", ".vcxproj", ".vcproj", ".xcodeproj", ".iml", ".dpr", ".vbp",
                       # 软件/游戏安装目录
                       ".dll", ".ocx", ".sys", ".so", ".jar", ".pak", ".wad",
                       # 数据库文件
                       ".frm", ".ibd", ".myd", ".mdf",
                       # 脚本与配置
                       ".sh", ".conf", ".properties", ".yml", ".yaml")
SOFTWARE_CONFIG_EXTS = (".ini", ".cfg", ".dat", ".bat")
SERVICE_SUBDIRS = {"lib", "conf", "config", "plugins", "modules"}

# 程序目录保护开启时，只有这些"独立资料文件"参与单文件去重；代码、配置、缓存等不做单文件去重
DOC_EXTS = frozenset((
    ".zip .rar .7z .tar .gz .tgz .bz2 .xz .cab .iso .gho .img .exe .msi .apk .ipa .dmg "
    ".pdf .doc .docx .xls .xlsx .ppt .pptx .wps .et .dps .rtf .txt .csv .chm .epub .mobi .caj .ofd "
    ".jpg .jpeg .png .gif .bmp .tif .tiff .webp .heic .psd .ai .cdr .dwg .dxf .eps .raw .cr2 .nef "
    ".mp3 .wav .flac .aac .m4a .wma .ape .ogg .amr "
    ".mp4 .avi .mkv .mov .wmv .flv .rmvb .rm .3gp .m4v .mpg .mpeg .vob").split())


def is_program_dir(name, names, dir_names):
    """name：目录名（小写）；names：目录下全部条目名（小写）；dir_names：其中的子目录名（小写）。"""
    if name.startswith("."):  # 隐藏的软件数据目录，如 .ADSPOWER_GLOBAL、.vscode
        return True
    if any(n in PROJECT_MARKERS or n.endswith(PROJECT_MARKER_EXTS) for n in names):
        return True
    exes = sum(1 for n in names if n.endswith(".exe"))
    # 软件：可执行文件 + 配置文件
    if exes and any(n.endswith(SOFTWARE_CONFIG_EXTS) for n in names):
        return True
    # 软件包：少量可执行文件 + 数据子目录（大量安装包堆放的资料目录不算）
    if 0 < exes <= 5 and dir_names:
        return True
    # 服务部署包：bin + lib/conf/…（如 elasticsearch、nacos、tomcat）
    return "bin" in dir_names and bool(SERVICE_SUBDIRS & dir_names)
CHUNK = 1024 * 1024
PARTIAL = 64 * 1024
FILE_ATTRIBUTE_REPARSE_POINT = 0x400

RULE_MTIME = "保留修改时间最早的（删除较新的）"
RULE_CTIME = "保留创建时间最早的（删除较新的）"
MODE_QUICK = "快速：名称+大小+修改时间+抽样（推荐）"
MODE_EXACT = "精确：逐个完整校验文件内容（慢）"

CONFIG_PATH = os.path.join(os.environ.get("APPDATA") or os.path.expanduser("~"),
                           "DupFinder", "config.json")


def load_config():
    try:
        with open(CONFIG_PATH, encoding="utf-8") as f:
            return json.load(f)
    except (OSError, ValueError):
        return {}


def save_config(cfg):
    try:
        os.makedirs(os.path.dirname(CONFIG_PATH), exist_ok=True)
        with open(CONFIG_PATH, "w", encoding="utf-8") as f:
            json.dump(cfg, f, ensure_ascii=False, indent=2)
    except OSError:
        pass


class Cancelled(Exception):
    pass


def fmt_size(n):
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024:
            return f"{n:.0f} {unit}" if unit == "B" else f"{n:.2f} {unit}"
        n /= 1024
    return f"{n:.2f} TB"


def fmt_time(t):
    return time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(t))


def norm(p):
    return os.path.normcase(os.path.normpath(p))


def birth_time(st):
    return getattr(st, "st_birthtime", st.st_ctime)


# ---------------------------------------------------------------- 扫描

class Scanner:
    """扫描目录，返回重复组的原始数据（不含删除决策）。"""

    def __init__(self, root, min_size, find_files, find_dirs, report, cancel_event, whitelist=(),
                 dep_dirs=None, quick=False):
        self.root = root
        self.quick = quick
        self.sample_cache = {}
        self.whitelist = {norm(p) for p in whitelist}
        self.whitelisted = 0
        # dep_dirs 为 None 表示关闭代码项目保护
        self.protect = dep_dirs is not None
        self.dep_dirs = {n.strip().lower() for n in (dep_dirs or ()) if n.strip()}
        self.dep_skipped = 0
        self.projects = 0
        self.min_size = max(1, min_size)
        self.find_files = find_files
        self.find_dirs = find_dirs
        self.report = report
        self.cancel = cancel_event
        self._last_report = 0.0
        self.files = []   # [path, size, mtime, ctime, dir_idx]
        self.dirs = []    # dict(path, parent, subdirs, files, mtime, ctime, incomplete)
        self.full_cache = {}
        self.errors = 0

    def _check(self):
        if self.cancel.is_set():
            raise Cancelled()

    def _status(self, text, force=False):
        now = time.time()
        if force or now - self._last_report > 0.2:
            self._last_report = now
            self.report(text)

    def run(self):
        self._walk()
        groups = []
        if self.find_dirs:
            groups += self._dir_groups()
        if self.find_files:
            groups += self._file_groups()
        return {"groups": groups, "file_count": len(self.files),
                "dir_count": len(self.dirs), "errors": self.errors,
                "whitelisted": self.whitelisted, "dep_skipped": self.dep_skipped,
                "projects": self.projects}

    # 遍历 ------------------------------------------------------------
    def _new_dir(self, path, parent, st):
        self.dirs.append({"path": path, "parent": parent, "subdirs": [], "files": [],
                          "mtime": st.st_mtime, "ctime": birth_time(st),
                          "incomplete": False, "project": False, "in_project": False})
        return len(self.dirs) - 1

    def _mark_incomplete(self, di):
        while di >= 0 and not self.dirs[di]["incomplete"]:
            self.dirs[di]["incomplete"] = True
            di = self.dirs[di]["parent"]

    def _walk(self):
        self._new_dir(self.root, -1, os.stat(self.root))
        stack = [0]
        while stack:
            self._check()
            di = stack.pop()
            d = self.dirs[di]
            self._status(f"正在遍历（{len(self.files)} 个文件）：{d['path']}")
            try:
                it = os.scandir(d["path"])
            except OSError:
                self.errors += 1
                self._mark_incomplete(di)
                continue
            names = []
            dir_names = set()
            dep_found = False
            with it:
                for e in it:
                    names.append(e.name.lower())
                    try:
                        st = e.stat(follow_symlinks=False)
                    except OSError:
                        self.errors += 1
                        self._mark_incomplete(di)
                        continue
                    if e.is_symlink() or getattr(st, "st_file_attributes", 0) & FILE_ATTRIBUTE_REPARSE_POINT:
                        continue
                    if stat.S_ISDIR(st.st_mode):
                        dir_names.add(e.name.lower())
                        # 系统目录与白名单目录不参与对比；其上级目录内容不完整，也不参与目录对比
                        if e.name.lower() in SKIP_DIRS or norm(e.path) in self.whitelist:
                            if norm(e.path) in self.whitelist:
                                self.whitelisted += 1
                            self._mark_incomplete(di)
                            continue
                        if self.protect and e.name.lower() in self.dep_dirs:
                            self.dep_skipped += 1
                            dep_found = True
                            continue
                        ci = self._new_dir(e.path, di, st)
                        d["subdirs"].append(ci)
                        stack.append(ci)
                    elif stat.S_ISREG(st.st_mode):
                        self.files.append([e.path, st.st_size, st.st_mtime, birth_time(st), di])
                        d["files"].append(len(self.files) - 1)
            if self.protect:
                d["project"] = is_program_dir(os.path.basename(d["path"]).lower(), names, dir_names)
                self.projects += d["project"] and not d["in_project"]
                for ci in d["subdirs"]:
                    self.dirs[ci]["in_project"] = d["in_project"] or d["project"]
                # 依赖目录只在项目内部可以忽略；项目外的同名目录内容未知，上级目录不参与目录对比
                if dep_found and not (d["project"] or d["in_project"]):
                    self._mark_incomplete(di)

    # 哈希 ------------------------------------------------------------
    def _hash(self, path, limit=None):
        h = hashlib.blake2b(digest_size=20)
        with open(path, "rb") as f:
            if limit:
                h.update(f.read(limit))
            else:
                while chunk := f.read(CHUNK):
                    self._check()
                    h.update(chunk)
        return h.digest()

    def _full_hash(self, fi):
        if fi in self.full_cache:
            return self.full_cache[fi]
        path, size = self.files[fi][0], self.files[fi][1]
        self._status(f"正在校验内容：{path}")
        try:
            digest = self._hash(path)
        except OSError:
            self.errors += 1
            digest = None
        self.full_cache[fi] = digest
        return digest

    def _head_hash(self, fi):
        path, size = self.files[fi][0], self.files[fi][1]
        try:
            digest = self._hash(path, PARTIAL)
        except OSError:
            self.errors += 1
            return None
        if size <= PARTIAL:
            self.full_cache[fi] = digest
        return digest

    def _sample_hash(self, fi):
        """快速模式：只读文件开头和结尾各 64KB；不超过 128KB 的文件等同于完整校验。"""
        if fi in self.sample_cache:
            return self.sample_cache[fi]
        path, size = self.files[fi][0], self.files[fi][1]
        h = hashlib.blake2b(digest_size=20)
        try:
            with open(path, "rb") as f:
                h.update(f.read(PARTIAL))
                if size > PARTIAL:
                    f.seek(max(PARTIAL, size - PARTIAL))
                    h.update(f.read(PARTIAL))
            digest = h.digest()
        except OSError:
            self.errors += 1
            digest = None
        if digest is not None and size <= 2 * PARTIAL:
            self.full_cache[fi] = digest
        self.sample_cache[fi] = digest
        return digest

    @staticmethod
    def _bucket(items, key_fn):
        buckets = {}
        for fi in items:
            k = key_fn(fi)
            if k is not None:
                buckets.setdefault(k, []).append(fi)
        return [b for b in buckets.values() if len(b) > 1]

    # 重复文件 --------------------------------------------------------
    def _file_groups(self):
        by_size = {}
        for fi, f in enumerate(self.files):
            owner = self.dirs[f[4]]
            if owner["project"] or owner["in_project"]:  # 项目内部文件不做文件级去重
                continue
            if self.protect and os.path.splitext(f[0])[1].lower() not in DOC_EXTS:
                continue
            if f[1] >= self.min_size:
                by_size.setdefault(f[1], []).append(fi)

        candidates = [g for g in by_size.values() if len(g) > 1]
        result = []
        for n, group in enumerate(candidates, 1):
            self._check()
            self._status(f"比对重复文件：第 {n}/{len(candidates)} 组", force=n == 1)
            if self.quick:
                buckets = self._bucket(group, self._sample_hash)
            else:
                buckets = [b for sub in self._bucket(group, self._head_hash)
                           for b in self._bucket(sub, self._full_hash)]
            for same in buckets:
                result.append({
                    "kind": "file", "size": self.files[same[0]][1], "count": 1,
                    "members": [self._file_member(fi) for fi in same]})
        return result

    def _file_member(self, fi):
        path, size, mtime, ctime, _ = self.files[fi]
        return {"path": path, "size": size, "mtime": mtime, "ctime": ctime}

    # 重复目录 --------------------------------------------------------
    def _dir_groups(self):
        self._status("正在计算目录结构特征…", force=True)
        n = len(self.dirs)
        total = [0] * n
        count = [0] * n
        cheap = [b""] * n
        top = [()] * n  # 快速模式：每个目录下最大的 3 个文件，用于抽样校验
        # 子目录索引总是大于父目录，倒序即自底向上
        for di in range(n - 1, -1, -1):
            d = self.dirs[di]
            h = hashlib.blake2b(digest_size=20)
            items = []
            for fi in d["files"]:
                name, size, mtime = os.path.basename(self.files[fi][0]), self.files[fi][1], self.files[fi][2]
                # 快速模式像人工一样看：文件名 + 大小 + 修改时间（按 2 秒取整，兼容 FAT/exFAT）
                items.append(f"f|{name}|{size}|{int(mtime) // 2}" if self.quick else f"f|{name}|{size}")
                total[di] += size
                count[di] += 1
            for ci in d["subdirs"]:
                items.append(f"d|{os.path.basename(self.dirs[ci]['path'])}|{cheap[ci].hex()}")
                total[di] += total[ci]
                count[di] += count[ci]
            for it in sorted(items):
                h.update(it.encode("utf-8", "surrogatepass") + b"\n")
            cheap[di] = h.digest()
            if self.quick:
                plen = len(d["path"])
                pool = list(d["files"]) + [fi for ci in d["subdirs"] for fi in top[ci]]
                top[di] = tuple(heapq.nlargest(3, pool, key=lambda fi: (self.files[fi][1],
                                                                        self.files[fi][0][plen:].lower())))

        by_cheap = {}
        for di in range(1, n):  # 跳过扫描根目录
            d = self.dirs[di]
            # 项目内部的子目录不参与对比，只有整个项目（或更上层目录）可作为重复目录
            if count[di] > 0 and total[di] >= self.min_size and not d["incomplete"] and not d["in_project"]:
                by_cheap.setdefault(cheap[di], []).append(di)
        candidates = [di for g in by_cheap.values() if len(g) > 1 for di in g]
        if not candidates:
            return []
        if self.quick:
            return self._quick_dir_groups(candidates, cheap, top, total, count)

        needed = set()
        stack = list(candidates)
        while stack:
            di = stack.pop()
            if di not in needed:
                needed.add(di)
                stack.extend(self.dirs[di]["subdirs"])

        exact = {}
        for di in sorted(needed, reverse=True):
            self._check()
            d = self.dirs[di]
            items = []
            ok = True
            for fi in d["files"]:
                digest = self._full_hash(fi)
                if digest is None:
                    ok = False
                    break
                items.append(f"f|{os.path.basename(self.files[fi][0])}|{digest.hex()}")
            if ok:
                for ci in d["subdirs"]:
                    if exact.get(ci) is None:
                        ok = False
                        break
                    items.append(f"d|{os.path.basename(self.dirs[ci]['path'])}|{exact[ci].hex()}")
            if not ok:
                exact[di] = None
                continue
            h = hashlib.blake2b(digest_size=20)
            for it in sorted(items):
                h.update(it.encode("utf-8", "surrogatepass") + b"\n")
            exact[di] = h.digest()

        by_exact = {}
        for di in candidates:
            if exact.get(di) is not None:
                by_exact.setdefault(exact[di], []).append(di)

        return self._dir_result(by_exact.values(), total, count)

    def _quick_dir_groups(self, candidates, cheap, top, total, count):
        by_key = {}
        for n, di in enumerate(candidates, 1):
            self._check()
            self._status(f"抽样校验重复目录：{n}/{len(candidates)}")
            plen = len(self.dirs[di]["path"])
            samples = []
            for fi in top[di]:
                digest = self._sample_hash(fi)
                if digest is None:
                    break
                samples.append((self.files[fi][0][plen:].lower(), digest))
            else:
                by_key.setdefault((cheap[di], tuple(samples)), []).append(di)
        return self._dir_result(by_key.values(), total, count)

    def _dir_result(self, buckets, total, count):
        result = []
        for same in buckets:
            if len(same) > 1:
                result.append({
                    "kind": "dir", "size": total[same[0]], "count": count[same[0]],
                    "members": [{"path": self.dirs[di]["path"], "size": total[di],
                                 "mtime": self.dirs[di]["mtime"],
                                 "ctime": self.dirs[di]["ctime"]} for di in same]})
        return result


def decide(raw_groups, rule):
    """按规则为每组决定保留项，并剔除位于"待删除目录"内的成员（避免重复处理）。"""
    def key(m):
        primary, secondary = (m["mtime"], m["ctime"]) if rule == RULE_MTIME else (m["ctime"], m["mtime"])
        return (primary, secondary, len(m["path"]), m["path"])

    def depth(g):
        return min(m["path"].count(os.sep) for m in g["members"])

    ordered = sorted((g for g in raw_groups if g["kind"] == "dir"), key=lambda g: (-g["size"], depth(g)))
    ordered += sorted((g for g in raw_groups if g["kind"] == "file"), key=lambda g: -g["size"])

    deleted_dirs = set()
    result = []
    for g in ordered:
        members = [dict(m) for m in g["members"] if not under_any(m["path"], deleted_dirs)]
        if len(members) < 2:
            continue
        members.sort(key=key)
        for i, m in enumerate(members):
            m["delete"] = i > 0
            m["state"] = ""
            if m["delete"] and g["kind"] == "dir":
                deleted_dirs.add(norm(m["path"]))
        result.append({**g, "members": members})
    return result


def under_any(path, dir_set):
    """path 是否位于 dir_set 中某个目录之内（或就是该目录）。"""
    if not dir_set:
        return False
    p = norm(path)
    while True:
        if p in dir_set:
            return True
        parent = os.path.dirname(p)
        if parent == p:
            return False
        p = parent


# ---------------------------------------------------------------- 删除

class SHFILEOPSTRUCTW(ctypes.Structure):
    _fields_ = [("hwnd", wintypes.HWND), ("wFunc", wintypes.UINT),
                ("pFrom", wintypes.LPCWSTR), ("pTo", wintypes.LPCWSTR),
                ("fFlags", ctypes.c_ushort), ("fAnyOperationsAborted", wintypes.BOOL),
                ("hNameMappings", ctypes.c_void_p), ("lpszProgressTitle", wintypes.LPCWSTR)]


def to_recycle_bin(path):
    try:
        from send2trash import send2trash
        send2trash(path)
        return
    except ImportError:
        pass
    buf = ctypes.create_unicode_buffer(os.path.abspath(path) + "\0")  # 双 \0 结尾
    op = SHFILEOPSTRUCTW()
    op.wFunc = 3  # FO_DELETE
    op.pFrom = ctypes.cast(buf, wintypes.LPCWSTR)
    # FOF_SILENT | FOF_NOCONFIRMATION | FOF_ALLOWUNDO | FOF_NOERRORUI | FOF_WANTNUKEWARNING
    op.fFlags = 0x4 | 0x10 | 0x40 | 0x400 | 0x4000
    rc = ctypes.windll.shell32.SHFileOperationW(ctypes.byref(op))
    if rc != 0 or op.fAnyOperationsAborted:
        raise OSError(f"移入回收站失败（代码 {rc}）")


def _force_writable(func, path, *_):
    os.chmod(path, stat.S_IWRITE)
    func(path)


def delete_permanently(path):
    if os.path.isdir(path):
        if sys.version_info >= (3, 12):
            shutil.rmtree(path, onexc=_force_writable)
        else:
            shutil.rmtree(path, onerror=_force_writable)
    else:
        try:
            os.remove(path)
        except PermissionError:
            os.chmod(path, stat.S_IWRITE)
            os.remove(path)


# ---------------------------------------------------------------- 界面

class App(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title(APP_TITLE)
        self.minsize(900, 560)
        self.queue = queue.Queue()
        self.cancel_event = threading.Event()
        self.worker = None
        self.raw_groups = []
        self.groups = []
        self.config_data = load_config()
        self.whitelist = [w for w in self.config_data.get("whitelist", []) if w.get("path")]

        self._build()
        self._center(1200, 720)
        self.after(100, self._poll)

    def _center(self, w, h):
        sw, sh = self.winfo_screenwidth(), self.winfo_screenheight()
        w, h = min(w, sw - 40), min(h, sh - 80)
        self.geometry(f"{w}x{h}+{(sw - w) // 2}+{max(0, (sh - h) // 2 - 20)}")

    def _build(self):
        top = ttk.Frame(self, padding=(10, 8))
        top.pack(fill="x")
        ttk.Label(top, text="扫描目录：").grid(row=0, column=0, sticky="w")
        self.root_var = tk.StringVar(value="E:\\")
        ttk.Entry(top, textvariable=self.root_var, width=50).grid(row=0, column=1, sticky="we")
        ttk.Button(top, text="浏览…", command=self._browse).grid(row=0, column=2, padx=4)
        ttk.Label(top, text="最小文件(KB)：").grid(row=0, column=3, padx=(12, 0))
        self.min_kb = tk.StringVar(value="0")
        ttk.Spinbox(top, from_=0, to=10 ** 7, textvariable=self.min_kb, width=8).grid(row=0, column=4)
        self.btn_scan = ttk.Button(top, text="开始扫描", command=self._start_scan)
        self.btn_scan.grid(row=0, column=5, padx=(12, 4))
        self.btn_stop = ttk.Button(top, text="停止", command=self._stop, state="disabled")
        self.btn_stop.grid(row=0, column=6)

        self.find_files = tk.BooleanVar(value=True)
        self.find_dirs = tk.BooleanVar(value=True)
        opts = ttk.Frame(top)
        opts.grid(row=1, column=1, sticky="w", pady=(6, 0))
        ttk.Checkbutton(opts, text="查找重复文件", variable=self.find_files).pack(side="left")
        ttk.Checkbutton(opts, text="查找重复目录", variable=self.find_dirs).pack(side="left", padx=(12, 0))
        ttk.Label(opts, text="对比方式：").pack(side="left", padx=(20, 0))
        self.mode = tk.StringVar(value=self.config_data.get("mode", MODE_QUICK))
        ttk.Combobox(opts, textvariable=self.mode, values=[MODE_QUICK, MODE_EXACT], state="readonly",
                     width=40).pack(side="left")
        ttk.Label(top, text="保留规则：").grid(row=1, column=3, sticky="e", pady=(6, 0))
        self.rule = tk.StringVar(value=RULE_MTIME)
        cb = ttk.Combobox(top, textvariable=self.rule, values=[RULE_MTIME, RULE_CTIME], state="readonly", width=32)
        cb.grid(row=1, column=4, columnspan=3, sticky="w", pady=(6, 0))
        cb.bind("<<ComboboxSelected>>", lambda e: self._apply_rule())
        self.protect = tk.BooleanVar(value=self.config_data.get("protect_projects", True))
        ttk.Checkbutton(top, text="程序目录保护（推荐）", variable=self.protect).grid(
            row=2, column=0, columnspan=2, sticky="w", pady=(6, 0))
        ttk.Label(top, text="跳过的依赖目录名：").grid(row=2, column=1, sticky="w", padx=(150, 0), pady=(6, 0))
        self.dep_dirs = tk.StringVar(value=self.config_data.get("dep_dirs", DEFAULT_DEP_DIRS))
        ttk.Entry(top, textvariable=self.dep_dirs).grid(row=2, column=1, columnspan=6, sticky="we",
                                                       padx=(270, 0), pady=(6, 0))
        top.columnconfigure(1, weight=1)

        wl = ttk.LabelFrame(self, text="白名单（勾选的目录及其所有子目录不参与重复对比，双击切换勾选）",
                            padding=(8, 4))
        wl.pack(fill="x", padx=10, pady=(0, 6))
        self.wl_tree = ttk.Treeview(wl, columns=("on", "path"), show="headings", height=3,
                                    selectmode="extended")
        self.wl_tree.heading("on", text="启用")
        self.wl_tree.heading("path", text="目录")
        self.wl_tree.column("on", width=60, anchor="center", stretch=False)
        self.wl_tree.column("path", width=700)
        self.wl_tree.pack(side="left", fill="x", expand=True)
        self.wl_tree.bind("<Double-1>", self._wl_on_double_click)
        wl_btns = ttk.Frame(wl)
        wl_btns.pack(side="left", padx=(8, 0))
        ttk.Button(wl_btns, text="添加目录…", command=self._wl_add).pack(fill="x")
        ttk.Button(wl_btns, text="勾选/取消", command=self._wl_toggle_selected).pack(fill="x", pady=2)
        ttk.Button(wl_btns, text="移除选中", command=self._wl_remove).pack(fill="x")
        self._wl_render()

        mid = ttk.Frame(self, padding=(10, 0))
        mid.pack(fill="both", expand=True)
        cols = ("state", "kind", "size", "mtime", "ctime")
        self.tree = ttk.Treeview(mid, columns=cols, selectmode="extended")
        self.tree.heading("#0", text="路径")
        for c, t, w in (("state", "处理", 70), ("kind", "类型", 60), ("size", "大小", 100),
                        ("mtime", "修改时间", 150), ("ctime", "创建时间", 150)):
            self.tree.heading(c, text=t)
            self.tree.column(c, width=w, anchor="center", stretch=False)
        self.tree.column("#0", width=600)
        self.tree.tag_configure("group", background="#eef3fb", font=("Microsoft YaHei UI", 9, "bold"))
        self.tree.tag_configure("keep", foreground="#1a7f37")
        self.tree.tag_configure("del", foreground="#cf222e")
        self.tree.tag_configure("done", foreground="#8c959f")
        ys = ttk.Scrollbar(mid, orient="vertical", command=self.tree.yview)
        xs = ttk.Scrollbar(mid, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=ys.set, xscrollcommand=xs.set)
        self.tree.grid(row=0, column=0, sticky="nsew")
        ys.grid(row=0, column=1, sticky="ns")
        xs.grid(row=1, column=0, sticky="we")
        mid.rowconfigure(0, weight=1)
        mid.columnconfigure(0, weight=1)
        self.tree.bind("<Double-1>", self._on_double_click)

        act = ttk.Frame(self, padding=(10, 6))
        act.pack(fill="x")
        ttk.Button(act, text="切换 保留/删除", command=self._toggle_selected).pack(side="left")
        ttk.Button(act, text="恢复默认标记", command=self._apply_rule).pack(side="left", padx=4)
        ttk.Button(act, text="全部展开", command=lambda: self._expand(True)).pack(side="left")
        ttk.Button(act, text="全部折叠", command=lambda: self._expand(False)).pack(side="left", padx=4)
        ttk.Button(act, text="导出列表(CSV)", command=self._export).pack(side="left")
        self.btn_delete = ttk.Button(act, text="删除标记项…", command=self._delete)
        self.btn_delete.pack(side="right")
        self.del_mode = tk.StringVar(value="recycle")
        ttk.Radiobutton(act, text="永久删除", value="permanent", variable=self.del_mode).pack(side="right", padx=6)
        ttk.Radiobutton(act, text="移入回收站", value="recycle", variable=self.del_mode).pack(side="right")
        self.summary = tk.StringVar(value="提示：双击条目可切换 保留/删除，每组至少保留一份。")
        ttk.Label(act, textvariable=self.summary, foreground="#0550ae").pack(side="left", padx=12)

        status = ttk.Frame(self, padding=(10, 0, 10, 4))
        status.pack(fill="x")
        self.progress = ttk.Progressbar(status, mode="determinate", length=160)
        self.progress.pack(side="right")
        self.status = tk.StringVar(value="就绪")
        ttk.Label(status, textvariable=self.status, anchor="w").pack(side="left", fill="x", expand=True)

        footer = tk.Label(self, text=FOOTER_TEXT, bg="#24292f", fg="#d0d7de",
                          font=("Microsoft YaHei UI", 9), pady=5)
        footer.pack(fill="x", side="bottom")

    # 白名单 ----------------------------------------------------------
    def _wl_render(self):
        self.wl_tree.delete(*self.wl_tree.get_children())
        for i, w in enumerate(self.whitelist):
            self.wl_tree.insert("", "end", iid=str(i), values=("☑" if w.get("enabled", True) else "☐", w["path"]))

    def _wl_save(self):
        self.config_data["whitelist"] = self.whitelist
        save_config(self.config_data)
        self._wl_render()

    def _wl_add(self):
        d = filedialog.askdirectory(initialdir=self.root_var.get() or "E:\\", title="选择白名单目录")
        if not d:
            return
        d = os.path.normpath(d)
        if any(norm(w["path"]) == norm(d) for w in self.whitelist):
            messagebox.showinfo(APP_TITLE, "该目录已在白名单中。")
            return
        self.whitelist.append({"path": d, "enabled": True})
        self._wl_save()

    def _wl_toggle(self, iid):
        w = self.whitelist[int(iid)]
        w["enabled"] = not w.get("enabled", True)

    def _wl_on_double_click(self, event):
        iid = self.wl_tree.identify_row(event.y)
        if iid:
            self._wl_toggle(iid)
            self._wl_save()
            return "break"

    def _wl_toggle_selected(self):
        for iid in self.wl_tree.selection():
            self._wl_toggle(iid)
        self._wl_save()

    def _wl_remove(self):
        drop = {int(i) for i in self.wl_tree.selection()}
        if drop:
            self.whitelist = [w for i, w in enumerate(self.whitelist) if i not in drop]
            self._wl_save()

    def active_whitelist(self):
        return [w["path"] for w in self.whitelist if w.get("enabled", True)]

    # 扫描 ------------------------------------------------------------
    def _browse(self):
        d = filedialog.askdirectory(initialdir=self.root_var.get() or "E:\\")
        if d:
            self.root_var.set(os.path.normpath(d))

    def _busy(self, busy):
        self.btn_scan.configure(state="disabled" if busy else "normal")
        self.btn_delete.configure(state="disabled" if busy else "normal")
        self.btn_stop.configure(state="normal" if busy else "disabled")
        if busy:
            self.progress.configure(mode="indeterminate")
            self.progress.start(12)
        else:
            self.progress.stop()
            self.progress.configure(mode="determinate", value=0)

    def _start_scan(self):
        root = self.root_var.get().strip()
        if not os.path.isdir(root):
            messagebox.showerror(APP_TITLE, f"目录不存在：{root}")
            return
        if not (self.find_files.get() or self.find_dirs.get()):
            messagebox.showwarning(APP_TITLE, "请至少勾选一种查找类型。")
            return
        try:
            min_size = int(float(self.min_kb.get() or 0) * 1024)
        except ValueError:
            messagebox.showerror(APP_TITLE, "最小文件大小请输入数字。")
            return
        whitelist = self.active_whitelist()
        if under_any(root, {norm(p) for p in whitelist}):
            messagebox.showwarning(APP_TITLE, "扫描目录本身位于白名单内，没有可对比的内容。")
            return
        self.config_data["protect_projects"] = self.protect.get()
        self.config_data["dep_dirs"] = self.dep_dirs.get()
        self.config_data["mode"] = self.mode.get()
        save_config(self.config_data)
        dep_dirs = self.dep_dirs.get().replace("，", ",").split(",") if self.protect.get() else None
        self.tree.delete(*self.tree.get_children())
        self.raw_groups, self.groups = [], []
        self.cancel_event.clear()
        self._busy(True)
        self.scan_start = time.time()
        scanner = Scanner(os.path.normpath(root), min_size, self.find_files.get(), self.find_dirs.get(),
                          lambda t: self.queue.put(("status", t)), self.cancel_event, whitelist, dep_dirs,
                          quick=self.mode.get() != MODE_EXACT)

        def work():
            try:
                self.queue.put(("scan_done", scanner.run()))
            except Cancelled:
                self.queue.put(("cancelled", None))
            except Exception as e:  # noqa: BLE001
                self.queue.put(("error", str(e)))

        self.worker = threading.Thread(target=work, daemon=True)
        self.worker.start()

    def _stop(self):
        self.cancel_event.set()
        self.status.set("正在停止…")

    def _poll(self):
        try:
            while True:
                kind, data = self.queue.get_nowait()
                if kind == "status":
                    self.status.set(data)
                elif kind == "scan_done":
                    self._busy(False)
                    self.raw_groups = data["groups"]
                    self._apply_rule()
                    self.status.set(f"扫描完成：{data['file_count']} 个文件，{data['dir_count']} 个目录，"
                                    f"程序目录 {data['projects']} 个，跳过依赖目录 {data['dep_skipped']} 个，"
                                    f"白名单 {data['whitelisted']} 个，无法读取 {data['errors']} 项，"
                                    f"用时 {time.time() - self.scan_start:.1f} 秒")
                elif kind == "cancelled":
                    self._busy(False)
                    self.status.set("已停止扫描")
                elif kind == "error":
                    self._busy(False)
                    self.status.set("出错")
                    messagebox.showerror(APP_TITLE, data)
                elif kind == "del_progress":
                    self.status.set(data)
                elif kind == "del_done":
                    self._busy(False)
                    self._after_delete(*data)
        except queue.Empty:
            pass
        self.after(100, self._poll)

    # 列表 ------------------------------------------------------------
    def _apply_rule(self):
        if not self.raw_groups:
            return
        self.groups = decide(self.raw_groups, self.rule.get())
        self._render()

    def _render(self):
        self.tree.delete(*self.tree.get_children())
        for gi, g in enumerate(self.groups):
            gid = f"g{gi}"
            self.tree.insert("", "end", iid=gid, text=self._group_text(gi, g), tags=("group",), open=True)
            for mi, m in enumerate(g["members"]):
                self.tree.insert(gid, "end", iid=f"{gid}_{mi}", text=m["path"],
                                 values=self._member_values(g, m), tags=(self._member_tag(m),))
        self._update_summary()

    def _group_text(self, gi, g):
        kind = "目录" if g["kind"] == "dir" else "文件"
        extra = f"，含 {g['count']} 个文件" if g["kind"] == "dir" else ""
        return f"第 {gi + 1} 组 · 重复{kind} × {len(g['members'])}{extra} · 每份 {fmt_size(g['size'])}"

    @staticmethod
    def _member_values(g, m):
        state = m["state"] or ("删除" if m["delete"] else "保留")
        return (state, "目录" if g["kind"] == "dir" else "文件", fmt_size(m["size"]),
                fmt_time(m["mtime"]), fmt_time(m["ctime"]))

    @staticmethod
    def _member_tag(m):
        if m["state"]:
            return "done"
        return "del" if m["delete"] else "keep"

    def _refresh_member(self, gi, mi):
        g, m = self.groups[gi], self.groups[gi]["members"][mi]
        self.tree.item(f"g{gi}_{mi}", values=self._member_values(g, m), tags=(self._member_tag(m),))

    def _update_summary(self):
        items = [(g, m) for g in self.groups for m in g["members"] if m["delete"] and not m["state"]]
        size = sum(m["size"] for _, m in items)
        self.summary.set(f"共 {len(self.groups)} 组重复，标记删除 {len(items)} 项，可释放 {fmt_size(size)}"
                         "（双击条目切换 保留/删除）")

    def _expand(self, open_):
        for gid in self.tree.get_children():
            self.tree.item(gid, open=open_)

    def _parse(self, iid):
        if "_" not in iid:
            return None
        g, m = iid[1:].split("_")
        return int(g), int(m)

    def _toggle(self, gi, mi):
        g = self.groups[gi]
        m = g["members"][mi]
        if m["state"]:
            return True
        if not m["delete"]:
            kept = [x for x in g["members"] if not x["delete"] and not x["state"]]
            if len(kept) <= 1:
                return False
        m["delete"] = not m["delete"]
        self._refresh_member(gi, mi)
        return True

    def _on_double_click(self, event):
        iid = self.tree.identify_row(event.y)
        pos = self._parse(iid) if iid else None
        if pos:
            if not self._toggle(*pos):
                messagebox.showinfo(APP_TITLE, "每组至少要保留一份。")
            self._update_summary()
            return "break"

    def _toggle_selected(self):
        refused = 0
        for iid in self.tree.selection():
            pos = self._parse(iid)
            if pos and not self._toggle(*pos):
                refused += 1
        self._update_summary()
        if refused:
            messagebox.showinfo(APP_TITLE, f"有 {refused} 项未切换：每组至少要保留一份。")

    def _export(self):
        if not self.groups:
            messagebox.showinfo(APP_TITLE, "没有可导出的内容，请先扫描。")
            return
        path = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV 文件", "*.csv")],
                                            initialfile="重复文件列表.csv")
        if not path:
            return
        with open(path, "w", newline="", encoding="utf-8-sig") as f:
            w = csv.writer(f)
            w.writerow(["组号", "类型", "处理", "路径", "大小(字节)", "修改时间", "创建时间"])
            for gi, g in enumerate(self.groups, 1):
                for m in g["members"]:
                    w.writerow([gi, "目录" if g["kind"] == "dir" else "文件",
                                m["state"] or ("删除" if m["delete"] else "保留"), m["path"], m["size"],
                                fmt_time(m["mtime"]), fmt_time(m["ctime"])])
        self.status.set(f"已导出：{path}")

    # 删除 ------------------------------------------------------------
    def _delete(self):
        targets = [(gi, mi) for gi, g in enumerate(self.groups)
                   for mi, m in enumerate(g["members"]) if m["delete"] and not m["state"]]
        if not targets:
            messagebox.showinfo(APP_TITLE, "没有标记为删除的条目。")
            return

        # 安全检查：每组必须有一份保留项，且它不在任何待删除目录之内
        del_dirs = {norm(self.groups[gi]["members"][mi]["path"]) for gi, mi in targets
                    if self.groups[gi]["kind"] == "dir"}
        for gi, g in enumerate(self.groups):
            if not any(m["delete"] for m in g["members"]):
                continue
            safe = [m for m in g["members"] if not m["delete"] and not m["state"]
                    and not under_any(m["path"], del_dirs)]
            if not safe:
                messagebox.showerror(APP_TITLE, f"第 {gi + 1} 组的保留项位于其他待删除目录中，"
                                     "删除后该内容将一份不剩。\n请调整标记后再删除。")
                self.tree.see(f"g{gi}")
                self.tree.selection_set(f"g{gi}")
                return

        size = sum(self.groups[gi]["members"][mi]["size"] for gi, mi in targets)
        permanent = self.del_mode.get() == "permanent"
        mode = "【永久删除，无法恢复】" if permanent else "移入回收站"
        if not messagebox.askyesno(APP_TITLE, f"即将{mode}：\n\n{len(targets)} 项，共 {fmt_size(size)}\n\n确定继续吗？",
                                   icon="warning"):
            return
        if permanent and not messagebox.askyesno(APP_TITLE, "再次确认：永久删除后无法从回收站恢复，确定吗？",
                                                 icon="warning"):
            return

        jobs = [(gi, mi, self.groups[gi]["kind"], dict(self.groups[gi]["members"][mi])) for gi, mi in targets]
        remover = delete_permanently if permanent else to_recycle_bin
        self._busy(True)
        self.btn_stop.configure(state="disabled")

        def work():
            results = []
            for n, (gi, mi, kind, m) in enumerate(jobs, 1):
                self.queue.put(("del_progress", f"正在删除 {n}/{len(jobs)}：{m['path']}"))
                path = m["path"]
                try:
                    if not os.path.exists(path):
                        results.append((gi, mi, "不存在", None))
                        continue
                    if kind == "file" and os.path.getsize(path) != m["size"]:
                        results.append((gi, mi, "已变化跳过", None))
                        continue
                    remover(path)
                    results.append((gi, mi, "已删除", None))
                except Exception as e:  # noqa: BLE001
                    results.append((gi, mi, "失败", f"{path}：{e}"))
            self.queue.put(("del_done", (results,)))

        threading.Thread(target=work, daemon=True).start()

    def _after_delete(self, results):
        failed = []
        freed = 0
        for gi, mi, state, err in results:
            m = self.groups[gi]["members"][mi]
            m["state"] = state
            if state == "已删除":
                freed += m["size"]
            if err:
                failed.append(err)
            self._refresh_member(gi, mi)
        self._update_summary()
        ok = sum(1 for r in results if r[2] == "已删除")
        self.status.set(f"删除完成：成功 {ok} 项，释放 {fmt_size(freed)}，失败 {len(failed)} 项")
        if failed:
            more = f"\n…等共 {len(failed)} 项" if len(failed) > 15 else ""
            messagebox.showwarning(APP_TITLE, "以下项目删除失败：\n\n" + "\n".join(failed[:15]) + more)


if __name__ == "__main__":
    try:
        ctypes.windll.shcore.SetProcessDpiAwareness(1)
    except Exception:  # noqa: BLE001
        pass
    App().mainloop()
