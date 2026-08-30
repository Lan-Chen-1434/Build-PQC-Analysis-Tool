# -*- coding: utf-8 -*-
"""
PQC 数据异常检测工具
检测7类异常：
  1. SN共用-破坏性测试      — 破坏性测试不允许共用SN
  2. SN共用-不同工站        — 不同工站不允许共用SN
  3. 数据异常-不同任务单测试值一致  — 不同任务单间测量值排序后高度一致
  4. 数据异常-不同人员数据分布不一致 — 单个人数据分布偏离整体
  5. 数据异常-测试数据规律性分布   — 数据呈规律性分布
  6. 数据异常-人员连续出现     — 检验人或修改人全局连续N天出现（N可配置，默认7）
  7. 数据异常-计量型测试值为空  — 计量型检测项（判断最小值/最大值其一为数值）的测量值为空

SN规则文件格式（5列）：
  序号 | 工站 | 要求 | 排除检测项 | 检测类型
  - 检测类型 = "破坏性测试" → 用于异常1
  - 检测类型 = "不同工站"   → 用于异常2
  - 排除检测项：在异常2中需要排除的检测项（如已由破坏性测试单独处理）
"""

import os
import re
import statistics
import sys
import threading
import queue
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext
from datetime import datetime
from collections import Counter, defaultdict
import json
import math

import pandas as pd
import numpy as np


# ==================== 常量 ====================


ANOMALY_TYPES = [
    'SN共用-破坏性测试',
    'SN共用-不同工站',
    '数据异常-不同任务单测试值一致',
    '数据异常-不同人员数据分布不一致',
    '数据异常-测试数据规律性分布',
    '数据异常-人员连续出现',
    '数据异常-计量型测试值为空',
]

# 异常3 阈值规则配置文件
# 打包成 exe 后存到 exe 所在目录，源码运行时存到源码目录
if getattr(sys, 'frozen', False):
    _BASE_DIR = os.path.dirname(sys.executable)
else:
    _BASE_DIR = os.path.dirname(os.path.abspath(__file__))
ANOMALY3_RULES_FILE = os.path.join(_BASE_DIR, 'anomaly3_rules.json')

# 异常3 默认阈值规则：（对比长度, 阈值）
# 含义：两条排序后的测量值序列，从第1位开始逐位对比，
#       若对比长度≥N，且匹配数量≥阈值M，则判为异常
DEFAULT_THRESHOLD_RULES = [
    (4, 3),
    (6, 5),
    (8, 6),
    (10, 8),
]


# ==================== SN 规则解析 ====================

def parse_sn_rules(df):
    """
    解析SN规则文件，支持两种列格式（自动检测）：

    旧格式（5列）：序号 | 工站 | 要求 | 排除检测项 | 检测类型
    新格式（6列）：序号 | 工站 | 要求 | SN可共用 | SN不共用 | 检测类型

    - 工站用逗号分割表示这些工站 SN 可以共用（同一分组）
    - SN检测项可共用：列出允许跨站共用 SN 的检测项（豁免项）
      带 ! 前缀的项表示排除项（如 !切片 表示排除切片检测）
    - SN检测项不共用：列出禁止共用 SN 的检测项

    返回:
    {
        'station_groups': {station_name: group_id},
        'group_info': {
            group_id: {
                stations,              # 工站名列表
                has_destructive,       # 是否有破坏性测试规则
                destructive_items,     # 破坏性检测项集合（来自规则文本解析）
                cross_forbidden,       # 是否禁止跨站
                cross_except_groups,   # 允许跨站的目标站点
                cross_except_items,    # 允许跨站的目标检测项
                excluded_items,        # 跨站检查时排除的检测项（旧格式）
                sn_shared_items,       # SN检测项可共用（豁免跨站检查）
                sn_exclude_items,      # SN检测项可共用中带!的项（排除项）
                sn_not_shared_items,   # SN检测项不共用
                destructive_req_texts, # 破坏性测试规则原文
                cross_req_texts,       # 不同工站规则原文
            }
        },
    }
    """
    station_groups = {}        # {station_name: group_id}
    group_rows = defaultdict(list)  # {group_id: [row_dict]}

    group_id = 0

    # 检测列数，自动适配新旧格式
    n_cols = len(df.columns) if len(df.columns) > 0 else len(df.iloc[0]) if len(df) > 0 else 5
    is_new_format = n_cols >= 6

    for _, row in df.iterrows():
        station_str = str(row.iloc[1]).strip() if len(row) > 1 and pd.notna(row.iloc[1]) else ''
        requirement = str(row.iloc[2]).strip() if len(row) > 2 and pd.notna(row.iloc[2]) else ''

        if is_new_format:
            # 新格式（6列）：序号 | 工站 | 要求 | SN可共用 | SN不共用 | 检测类型
            sn_shared_str = str(row.iloc[3]).strip() if len(row) > 3 and pd.notna(row.iloc[3]) else ''
            sn_not_shared_str = str(row.iloc[4]).strip() if len(row) > 4 and pd.notna(row.iloc[4]) else ''
            excluded_str = ''  # 新格式无"排除检测项"列
            detection_type = str(row.iloc[5]).strip() if len(row) > 5 and pd.notna(row.iloc[5]) else ''
        else:
            # 旧格式（5列）：序号 | 工站 | 要求 | 排除检测项 | 检测类型
            excluded_str = str(row.iloc[3]).strip() if len(row) > 3 and pd.notna(row.iloc[3]) else ''
            sn_shared_str = ''
            sn_not_shared_str = ''
            detection_type = str(row.iloc[4]).strip() if len(row) > 4 and pd.notna(row.iloc[4]) else ''

        if not station_str or station_str.lower() == 'nan':
            continue

        # 拆分多个工站名（用 、或 , 分隔）→ 同组工站SN可共用
        parts = [p.strip() for p in re.split(r'[、,，]', station_str) if p.strip()]
        if not parts:
            continue

        # 检查是否与已有分组重叠（合并到已有分组）
        found_gid = None
        for p in parts:
            if p in station_groups:
                found_gid = station_groups[p]
                break

        if found_gid is not None:
            current_gid = found_gid
            for p in parts:
                if p not in station_groups:
                    station_groups[p] = current_gid
        else:
            current_gid = group_id
            group_id += 1
            for p in parts:
                station_groups[p] = current_gid

        # 解析排除检测项（旧格式）
        excluded_items = set()
        if excluded_str and excluded_str.lower() != 'nan':
            for item in re.split(r'[、,，]', excluded_str):
                item = item.strip()
                if item:
                    excluded_items.add(item)

        # 解析 SN检测项可共用（不带!的 = 豁免项，带!的 = 排除项）
        sn_shared_items = set()
        sn_exclude_items = set()
        if sn_shared_str and sn_shared_str.lower() != 'nan':
            for item in re.split(r'[、,，]', sn_shared_str):
                item = item.strip()
                if not item:
                    continue
                if item.startswith('!'):
                    # !切片 → 排除"切片"检测项
                    sn_exclude_items.add(item[1:])
                else:
                    sn_shared_items.add(item)

        # 解析 SN检测项不共用 检测项
        sn_not_shared_items = set()
        if sn_not_shared_str and sn_not_shared_str.lower() != 'nan':
            for item in re.split(r'[、,，]', sn_not_shared_str):
                item = item.strip()
                if item:
                    sn_not_shared_items.add(item)

        group_rows[current_gid].append({
            'stations': parts,
            'requirement': requirement,
            'excluded_items': excluded_items,
            'sn_shared_items': sn_shared_items,
            'sn_exclude_items': sn_exclude_items,
            'sn_not_shared_items': sn_not_shared_items,
            'detection_type': detection_type,
        })

    # 合并分组信息
    group_info = {}
    for gid, rows in group_rows.items():
        all_stations = []
        destructive_reqs = []
        cross_reqs = []
        all_excluded_items = set()

        all_sn_shared_items = set()
        all_sn_exclude_items = set()
        all_sn_not_shared_items = set()

        for r in rows:
            for s in r['stations']:
                if s not in all_stations:
                    all_stations.append(s)

            dt = r['detection_type']
            if dt == '破坏性测试':
                destructive_reqs.append(r['requirement'])
            elif dt == '不同工站':
                cross_reqs.append(r['requirement'])
                all_excluded_items.update(r['excluded_items'])

            all_sn_shared_items.update(r.get('sn_shared_items', set()))
            all_sn_exclude_items.update(r.get('sn_exclude_items', set()))
            all_sn_not_shared_items.update(r.get('sn_not_shared_items', set()))

        # 解析破坏性测试规则文本
        destructive_items, cross_except_groups, cross_except_items, shared_items = \
            _parse_destructive_requirements(destructive_reqs)

        # 解析不同工站规则文本
        cross_forbidden = False
        for req in cross_reqs:
            if '不用于其他工站' in req or '不用于其他测试' in req:
                cross_forbidden = True
        if cross_reqs:
            cross_forbidden = True  # 有"不同工站"规则即表示要检查跨站

        group_info[gid] = {
            'stations': all_stations,
            'has_destructive': len(destructive_reqs) > 0,
            'destructive_items': destructive_items,
            'cross_forbidden': cross_forbidden,
            'cross_except_groups': cross_except_groups,
            'cross_except_items': cross_except_items,
            'shared_items': shared_items,
            'excluded_items': all_excluded_items,
            'sn_shared_items': all_sn_shared_items,
            'sn_exclude_items': all_sn_exclude_items,
            'sn_not_shared_items': all_sn_not_shared_items,
            'destructive_req_texts': destructive_reqs,
            'cross_req_texts': cross_reqs,
        }

    return {
        'station_groups': station_groups,
        'group_info': group_info,
        'group_count': len(group_info),
    }


def _parse_destructive_requirements(requirements):
    """
    解析破坏性测试规则文本，提取：
    - destructive_items: 破坏性检测项（SN不能复用）
    - cross_except_groups: 跨站例外目标站点
    - cross_except_items: 跨站例外检测项
    - shared_items: 可共用SN的检测项
    """
    destructive_items = set()
    cross_except_groups = set()
    cross_except_items = set()
    shared_items = set()

    full_text = '；'.join(requirements)

    # ---------- 破坏性检测项 ----------
    # "XXSN不能共用" 或 "XX、YYSN不能共用"
    no_share = re.search(r'([^，。,;；]+?)(?:SN|的SN)\s*不能共用', full_text)
    if no_share:
        items_part = no_share.group(1)
        for item in re.split(r'[、,，]', items_part):
            item = item.strip()
            if item:
                destructive_items.add(item)

    # "XX SN不用于YY" → XX 是破坏性的
    for m in re.finditer(r'([^\s,，、]+)\s*SN\s*不用于', full_text):
        item = m.group(1).strip()
        if item:
            destructive_items.add(item)

    # 明确的关键词匹配
    for kw in ['X-ray', 'X-Ray', '拉拔力', '切片', '油浴', '最终封存量']:
        if kw in full_text and ('SN' in full_text):
            destructive_items.add(kw)

    # ---------- 可共用项 ----------
    if re.search(r'外观.*SN.*可共用', full_text):
        shared_items.add('外观')
    if re.search(r'测量尺寸.*可共用|尺寸.*可共用', full_text):
        shared_items.add('尺寸')

    # ---------- 跨站例外 ----------
    # "可用于XX"
    for m in re.finditer(r'可用于(.+?)(?:[，,。;；]|$)', full_text):
        cu = m.group(1).strip()
        if '二除' in cu or '二次除气' in cu:
            cross_except_groups.add('二次除气')
            if '尺寸' in cu:
                cross_except_items.add('尺寸')

    # "除XX，不用于其他工站" 或 "除XX外，不用于其他工站"
    for m in re.finditer(r'除(.+?)[，,]?\s*不用于其他', full_text):
        exc_text = m.group(1).strip()
        if '二次除气' in exc_text or '二除' in exc_text:
            cross_except_groups.add('二次除气')
        if '以上' not in exc_text and '要求' not in exc_text:
            # 具体站点名
            pass

    return destructive_items, cross_except_groups, cross_except_items, shared_items


# ==================== GUI 主应用 ====================

class PQCApp:
    """PQC 数据分析工具 - 7项异常检测"""

    def __init__(self, root):
        self.root = root
        self.root.title('PQC 数据分析 - 异常检测（v1.4）')
        self.root.geometry('1300x950+350+80')
        try:
            self.root.state('zoomed')  # 启动默认最大化（Windows）
        except tk.TclError:
            try:
                self.root.attributes('-zoomed', True)  # Linux 回退
            except tk.TclError:
                pass  # macOS 不支持该属性，直接跳过
        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(5, weight=1)

        self.filepath = tk.StringVar()
        self.rulepath = tk.StringVar()
        self.status_text = tk.StringVar(value='请选择数据文件（SN规则文件可选）...')

        self.df = None
        self.anomalies = []
        self.rules = None
        self.inspection_items = []  # 从SN规则第二sheet加载的检验项目列表

        # 异常3 阈值规则：从文件加载，失败则用默认值
        loaded = self._load_threshold_rules()
        self.threshold_rules = loaded if loaded else DEFAULT_THRESHOLD_RULES[:]

        # 异常6 连续天数阈值
        self.consecutive_days_var = tk.IntVar(value=7)

        # 默认列名映射
        self.col_task = tk.StringVar(value='任务单号')
        self.col_item = tk.StringVar(value='检验项目')
        self.col_content = tk.StringVar(value='检验内容')
        self.col_person = tk.StringVar(value='检验人')
        self.col_value = tk.StringVar(value='测量值')
        self.col_sn = tk.StringVar(value='SN')
        self.col_item_type = tk.StringVar(value='项目类型')
        self.col_station = tk.StringVar(value='适用站点')
        self.col_spec_min = tk.StringVar(value='判断最小值')
        self.col_spec_max = tk.StringVar(value='判断最大值')
        self.col_scan_time = tk.StringVar(value='扫入时间')
        self.col_modifier = tk.StringVar(value='测量值修改人')
        self.col_modify_time = tk.StringVar(value='测量值修改时间')
        self.col_result = tk.StringVar(value='结果')

        # 跨线程UI更新队列：macOS 禁止在后台线程直接操作 Tk 控件，
        # 后台线程一律经 _ui_post 投递，由主线程定时器统一执行
        self._ui_queue = queue.Queue()

        self._build_ui()
        self.root.after(100, self._drain_ui_queue)

    def _ui_post(self, fn):
        """后台线程安全地调度UI操作（投递到主线程执行）"""
        self._ui_queue.put(fn)

    def _ui_log(self, msg):
        """线程安全版本的 _log"""
        self._ui_post(lambda: self._log(msg))

    def _drain_ui_queue(self):
        """主线程定时器：取出后台线程投递的UI操作并执行"""
        try:
            while True:
                fn = self._ui_queue.get_nowait()
                try:
                    fn()
                except Exception:
                    import traceback
                    traceback.print_exc()
        except queue.Empty:
            pass
        self.root.after(100, self._drain_ui_queue)

    # ==================== UI 构建 ====================

    def _build_ui(self):
        # --- 第0行：文件选择 ---
        file_frame = ttk.LabelFrame(self.root, text='文件选择', padding=5)
        file_frame.grid(row=0, column=0, sticky='ew', padx=5, pady=3)
        file_frame.columnconfigure(1, weight=1)

        ttk.Button(file_frame, text='选择数据文件', command=self._select_file).grid(
            row=0, column=0, sticky='w', padx=3)
        ttk.Entry(file_frame, textvariable=self.filepath, state='readonly').grid(
            row=0, column=1, sticky='ew', padx=3)
        ttk.Button(file_frame, text='开始分析', command=self._start_analysis).grid(
            row=0, column=2, sticky='e', padx=3)
        ttk.Button(file_frame, text='导出结果', command=self._export_results).grid(
            row=0, column=3, sticky='e', padx=3)

        # --- 第1行：列名映射（跟随窗口宽度自动换行） ---
        col_frame = ttk.LabelFrame(self.root, text='列名映射（与默认一致则无需修改）', padding=5)
        col_frame.grid(row=1, column=0, sticky='ew', padx=5, pady=3)

        labels_vars = [
            ('任务单号:', self.col_task),
            ('检验项目:', self.col_item),
            ('检验内容:', self.col_content),
            ('检验人:', self.col_person),
            ('测量值:', self.col_value),
            ('SN:', self.col_sn),
            ('项目类型:', self.col_item_type),
            ('适用站点:', self.col_station),
            ('判断最小值:', self.col_spec_min),
            ('判断最大值:', self.col_spec_max),
            ('扫入时间:', self.col_scan_time),
            ('测量值修改人:', self.col_modifier),
            ('测量值修改时间:', self.col_modify_time),
            ('结果:', self.col_result),
        ]
        self._colmap_frame = col_frame
        self._colmap_pairs = []
        self._colmap_cols = 0  # 当前每行组数（0 = 尚未布局）
        for label, var in labels_vars:
            pair = ttk.Frame(col_frame)
            ttk.Label(pair, text=label).pack(side=tk.LEFT, padx=1)
            ttk.Entry(pair, textvariable=var, width=12).pack(side=tk.LEFT, padx=1)
            self._colmap_pairs.append(pair)
        col_frame.bind('<Configure>', self._relayout_colmap)

        # --- 第2行：SN规则文件 ---
        sn_frame = ttk.LabelFrame(self.root, text='SN 共用规则文件（6列：序号|工站|要求|SN检测项可共用|SN检测项不共用|检测类型）', padding=5)
        sn_frame.grid(row=2, column=0, sticky='ew', padx=5, pady=3)

        ttk.Button(sn_frame, text='选择 SN 规则文件', command=self._load_sn_rules).pack(
            side=tk.LEFT, padx=5)
        ttk.Entry(sn_frame, textvariable=self.rulepath, state='readonly').pack(
            side=tk.LEFT, fill=tk.X, expand=True, padx=5)
        self.sn_rules_status = tk.StringVar(value='')
        ttk.Label(sn_frame, textvariable=self.sn_rules_status, foreground='gray').pack(
            side=tk.RIGHT, padx=10)

        # --- 第3行：异常3 对比长度阈值规则设置 ---
        threshold_frame = ttk.LabelFrame(self.root, text='异常3 对比长度阈值规则（对比长度≥N 时，匹配数量≥阈值M 则判异常）', padding=5)
        threshold_frame.grid(row=3, column=0, sticky='ew', padx=5, pady=3)

        self.threshold_entries = []  # [(len_var, threshold_var), ...]
        header_frame = ttk.Frame(threshold_frame)
        header_frame.pack(side=tk.TOP, fill=tk.X)

        ttk.Label(header_frame, text='对比长度', font=('', 8)).pack(side=tk.LEFT, padx=2)
        ttk.Label(header_frame, text='≥阈值', font=('', 8)).pack(side=tk.LEFT, padx=2)
        ttk.Label(header_frame, text='   ').pack(side=tk.LEFT)

        for rule_len, rule_threshold in self.threshold_rules:
            self._add_threshold_row(threshold_frame, rule_len, rule_threshold)

        btn_frame = ttk.Frame(threshold_frame)
        btn_frame.pack(side=tk.BOTTOM, fill=tk.X, pady=(5, 0))
        ttk.Button(btn_frame, text='+ 添加规则', command=lambda: self._add_threshold_row(threshold_frame, '', '')).pack(
            side=tk.LEFT, padx=3)
        ttk.Button(btn_frame, text='保存规则', command=self._save_threshold_rules).pack(side=tk.RIGHT, padx=3)
        ttk.Button(btn_frame, text='加载规则', command=self._load_and_apply_threshold_rules).pack(side=tk.RIGHT, padx=3)

        self.skip_ok = tk.BooleanVar(value=False)
        ttk.Checkbutton(btn_frame, text='仅分析结果=OK的行',
                        variable=self.skip_ok).pack(side=tk.RIGHT, padx=10)
        ttk.Spinbox(btn_frame, textvariable=self.consecutive_days_var,
                    from_=2, to=30, width=3).pack(side=tk.RIGHT, padx=2)
        ttk.Label(btn_frame, text='异常连续天数:').pack(side=tk.RIGHT)

        # --- 第4行：检测异常类型筛选（跟随窗口宽度自动换行） ---
        self.filter_frame = ttk.LabelFrame(self.root, text='检测异常类型', padding=5)
        self.filter_frame.grid(row=4, column=0, sticky='ew', padx=5, pady=2)

        self.show_types = {}
        self._filter_cbs = []
        self._filter_cols = 0  # 当前每行复选框数量（0 = 尚未布局）
        for i, atype in enumerate(ANOMALY_TYPES):
            var = tk.BooleanVar(value=True)
            self.show_types[atype] = var
            cb = ttk.Checkbutton(self.filter_frame, text=f'异常{i + 1}：{atype}',
                                 variable=var, command=self._refresh_tree)
            self._filter_cbs.append(cb)

        self.filter_frame.bind('<Configure>', self._relayout_filter)

        # --- 第5行：标签页（日志 / 检验项目分析 / 异常数据汇总），高度随窗口自适应 ---
        # 自绘标签栏：ttk.Notebook 在 Windows 原生主题下不支持 hover 变色，
        # 用 tk 控件实现悬停高亮和选中高亮。
        self._current_tab = None
        self._tab_buttons = {}
        self._tab_pages = {}

        tab_area = ttk.Frame(self.root)
        tab_area.grid(row=5, column=0, sticky='nsew', padx=5, pady=2)
        tab_area.columnconfigure(0, weight=1)
        tab_area.rowconfigure(1, weight=1)

        self._tab_bar = tk.Frame(tab_area)
        self._tab_bar.grid(row=0, column=0, sticky='ew')

        page_area = tk.Frame(tab_area)
        page_area.grid(row=1, column=0, sticky='nsew')
        page_area.columnconfigure(0, weight=1)
        page_area.rowconfigure(0, weight=1)
        self._tab_page_area = page_area

        # 标签1：日志（sunken 边框形成嵌入效果）
        tab_log = self._make_tab('日志')
        tab_log.columnconfigure(0, weight=1)
        tab_log.rowconfigure(0, weight=1)

        self.log_text = scrolledtext.ScrolledText(tab_log, height=3, font=('宋体', 10))
        self.log_text.grid(row=0, column=0, sticky='nsew', padx=2, pady=2)

        # 标签2：检验项目分析（sunken 边框形成嵌入效果）
        tab_inspect = self._make_tab('检验项目分析')
        tab_inspect.columnconfigure(0, weight=1)
        tab_inspect.rowconfigure(0, weight=1)

        inspect_frame = ttk.LabelFrame(tab_inspect, text='双击查看详细统计', padding=5)
        inspect_frame.grid(row=0, column=0, sticky='nsew', padx=3, pady=3)
        inspect_frame.columnconfigure(0, weight=1)
        inspect_frame.rowconfigure(0, weight=1)

        list_frame = ttk.Frame(inspect_frame)
        list_frame.grid(row=0, column=0, sticky='nsew')
        list_frame.columnconfigure(0, weight=1)
        list_frame.rowconfigure(0, weight=1)

        scrollbar_il = ttk.Scrollbar(list_frame, orient=tk.VERTICAL)
        self.inspect_listbox = tk.Listbox(
            list_frame, height=4, yscrollcommand=scrollbar_il.set,
            font=('微软雅黑', 10), exportselection=False
        )
        scrollbar_il.config(command=self.inspect_listbox.yview)

        self.inspect_listbox.grid(row=0, column=0, sticky='nsew')
        scrollbar_il.grid(row=0, column=1, sticky='ns')

        self.inspect_listbox.bind('<Double-1>', self._on_inspection_double_click)

        btn_frame_inspect = ttk.Frame(inspect_frame)
        btn_frame_inspect.grid(row=0, column=1, sticky='ns', padx=(5, 0))
        ttk.Button(btn_frame_inspect, text='查看详情',
                   command=self._on_inspection_detail_click).pack(side=tk.TOP, pady=2)

        self.inspect_status = tk.StringVar(value='')
        ttk.Label(inspect_frame, textvariable=self.inspect_status, foreground='gray').grid(
            row=1, column=0, sticky='w', padx=3)

        # --- 标签3：异常数据汇总（结果表格，sunken 边框形成嵌入效果） ---
        tab_tree = self._make_tab('异常数据汇总')
        tab_tree.columnconfigure(0, weight=1)
        tab_tree.rowconfigure(0, weight=1)

        tree_frame = ttk.Frame(tab_tree)
        tree_frame.grid(row=0, column=0, sticky='nsew', padx=3, pady=3)
        tree_frame.columnconfigure(0, weight=1)
        tree_frame.rowconfigure(0, weight=1)

        columns = ('index', 'type', 'detail1', 'detail2', 'detail3', 'detail4', 'detail5')
        self.tree = ttk.Treeview(tree_frame, columns=columns, show='headings', selectmode='extended')

        self.tree.heading('index', text='序号')
        self.tree.heading('type', text='异常类型')
        self.tree.heading('detail1', text='检验项目/SN')
        self.tree.heading('detail2', text='检验人/站点')
        self.tree.heading('detail3', text='任务单/统计信息')
        self.tree.heading('detail4', text='详情')
        self.tree.heading('detail5', text='备注')

        self.tree.column('index', width=45, anchor='center')
        self.tree.column('type', width=230, anchor='w')
        self.tree.column('detail1', width=220, anchor='w')
        self.tree.column('detail2', width=180, anchor='w')
        self.tree.column('detail3', width=180, anchor='w')
        self.tree.column('detail4', width=280, anchor='w')
        self.tree.column('detail5', width=180, anchor='w')

        scrollbar_y = ttk.Scrollbar(tree_frame, orient=tk.VERTICAL, command=self.tree.yview)
        scrollbar_x = ttk.Scrollbar(tree_frame, orient=tk.HORIZONTAL, command=self.tree.xview)
        self.tree.configure(yscrollcommand=scrollbar_y.set, xscrollcommand=scrollbar_x.set)

        self.tree.grid(row=0, column=0, sticky='nsew')
        scrollbar_y.grid(row=0, column=1, sticky='ns')
        scrollbar_x.grid(row=1, column=0, sticky='ew')

        self.tree.bind('<Double-1>', self._on_double_click)

        # 默认显示“日志”标签页
        self._switch_tab('日志')

        # --- 状态栏（绿色进度条与进度文字重叠显示，同一行） ---
        self._progress_pct = 0
        self.status_canvas = tk.Canvas(self.root, height=20, highlightthickness=1,
                                       highlightbackground='#999', bg='#e9ecef')
        self.status_canvas.grid(row=6, column=0, sticky='ew', padx=5, pady=2)
        self.status_canvas.bind('<Configure>', lambda e: self._redraw_status())
        # status_text 任何改动（含错误提示）都触发重绘
        self.status_text.trace_add('write', lambda *_: self._redraw_status())

    # ==================== 标签页切换 ====================

    # 标签按钮配色：常态 / 悬停 / 选中
    TAB_BG_NORMAL = '#e1e1e1'
    TAB_BG_HOVER = '#9ecbff'
    TAB_BG_SELECTED = '#0078d7'

    def _make_tab(self, name):
        """创建一个标签按钮 + 对应页面（sunken 嵌入效果），返回页面容器"""
        page = tk.Frame(self._tab_page_area, relief=tk.SUNKEN, bd=2)
        page.grid(row=0, column=0, sticky='nsew')
        btn = tk.Label(self._tab_bar, text=name,
                       font=('微软雅黑', 10, 'bold'), padx=16, pady=4,
                       bg=self.TAB_BG_NORMAL, relief=tk.RAISED, bd=1,
                       cursor='hand2')
        btn.pack(side=tk.LEFT, padx=(3, 0), pady=(3, 0))
        btn.bind('<Button-1>', lambda e, n=name: self._switch_tab(n))
        btn.bind('<Enter>', lambda e, n=name: self._on_tab_hover(n, True))
        btn.bind('<Leave>', lambda e, n=name: self._on_tab_hover(n, False))
        self._tab_buttons[name] = btn
        self._tab_pages[name] = page
        return page

    def _switch_tab(self, name):
        """切换到指定标签页"""
        self._current_tab = name
        self._tab_pages[name].tkraise()
        for n, btn in self._tab_buttons.items():
            if n == name:
                btn.config(bg=self.TAB_BG_SELECTED, fg='white', relief=tk.SUNKEN)
            else:
                btn.config(bg=self.TAB_BG_NORMAL, fg='black', relief=tk.RAISED)

    def _on_tab_hover(self, name, entering):
        """悬停高亮（选中的标签不变色）"""
        if name == self._current_tab:
            return
        self._tab_buttons[name].config(
            bg=self.TAB_BG_HOVER if entering else self.TAB_BG_NORMAL)

    def _report_progress(self, msg, pct):
        """更新状态文本和进度百分比（重绘由 trace 触发）"""
        self._progress_pct = pct
        self.status_text.set(msg)

    def _redraw_status(self):
        """在状态栏画布上重绘绿色进度条和进度文字（重叠）

        绿条与外框之间留出内边距，形成嵌入槽内的显示效果。
        """
        c = self.status_canvas
        c.delete('all')
        w = c.winfo_width()
        h = c.winfo_height()
        if w <= 1:
            return
        m = 3  # 内边距：绿条嵌入外框之内
        pct = max(0, min(100, self._progress_pct))
        inner_w = w - 2 * m
        fill_w = int(inner_w * pct / 100)
        if fill_w > 0:
            c.create_rectangle(m, m, m + fill_w, h - m, fill='#28a745', outline='')
        c.create_text(m + 4, h // 2, anchor='w', text=self.status_text.get(),
                      font=('微软雅黑', 9))

    @staticmethod
    def _fit_columns(frame, widgets, pad=8):
        """根据容器实际宽度，计算一行能放下多少个子控件（放不下时至少1个）"""
        width = frame.winfo_width()
        if width <= 1 or not widgets:
            return 0
        cols = 0
        used = 0
        for w in widgets:
            ww = w.winfo_reqwidth() + pad
            if cols > 0 and used + ww > width:
                break
            used += ww
            cols += 1
        return max(cols, 1)

    def _relayout_colmap(self, event=None):
        """根据列名映射区实际宽度自动换行排列 标签+输入框 组"""
        cols = self._fit_columns(self._colmap_frame, self._colmap_pairs)
        if cols == 0 or cols == self._colmap_cols:
            return
        self._colmap_cols = cols
        for i, pair in enumerate(self._colmap_pairs):
            pair.grid(row=i // cols, column=i % cols, sticky='w', padx=4)

    def _relayout_filter(self, event=None):
        """根据筛选区实际宽度自动换行排列异常类型复选框"""
        cols = self._fit_columns(self.filter_frame, self._filter_cbs)
        if cols == 0 or cols == self._filter_cols:
            return  # 布局未变化，避免重复重排
        self._filter_cols = cols

        for i, cb in enumerate(self._filter_cbs):
            cb.grid(row=i // cols, column=i % cols, sticky='w', padx=4)

    # ==================== 阈值规则管理 ====================

    def _add_threshold_row(self, parent, len_val, threshold_val):
        """在阈值面板中添加一行规则输入"""
        row_frame = ttk.Frame(parent)
        row_frame.pack(side=tk.TOP, fill=tk.X, pady=1)

        len_var = tk.StringVar(value=str(len_val))
        threshold_var = tk.StringVar(value=str(threshold_val))

        ttk.Label(row_frame, text='对比长度 ≥').pack(side=tk.LEFT, padx=2)
        ttk.Entry(row_frame, textvariable=len_var, width=6).pack(side=tk.LEFT, padx=2)
        ttk.Label(row_frame, text='  匹配数量 ≥').pack(side=tk.LEFT, padx=2)
        ttk.Entry(row_frame, textvariable=threshold_var, width=6).pack(side=tk.LEFT, padx=2)

        def _remove_row():
            self.threshold_entries[:] = [
                (lv, tv, rf) for lv, tv, rf in self.threshold_entries
                if rf is not row_frame
            ]
            row_frame.destroy()

        ttk.Button(row_frame, text='✕', width=2, command=_remove_row).pack(side=tk.LEFT, padx=5)

        self.threshold_entries.append((len_var, threshold_var, row_frame))
    def _collect_threshold_rules(self):
        """从UI输入中收集当前阈值规则，返回 [(对比长度, 阈值), ...]"""
        rules = []
        for len_var, threshold_var, _ in self.threshold_entries:
            try:
                compare_len = int(len_var.get().strip())
                threshold = int(threshold_var.get().strip())
                if compare_len > 0 and threshold > 0 and threshold <= compare_len:
                    rules.append((compare_len, threshold))
            except ValueError:
                continue
        return rules

    def _save_threshold_rules(self):
        """保存阈值规则到本地JSON文件"""
        rules = self._collect_threshold_rules()
        if not rules:
            messagebox.showwarning('提示', '没有有效的阈值规则可保存')
            return

        rules.sort(key=lambda x: x[0])  # 按对比长度升序保存

        try:
            with open(ANOMALY3_RULES_FILE, 'w', encoding='utf-8') as f:
                json.dump(rules, f, ensure_ascii=False, indent=2)
            self.threshold_rules = rules
            self._log(f'阈值规则已保存到: {ANOMALY3_RULES_FILE}')
            messagebox.showinfo('成功', f'已保存 {len(rules)} 条阈值规则')
        except Exception as e:
            messagebox.showerror('错误', f'保存失败: {e}')

    def _load_and_apply_threshold_rules(self):
        """加载并应用本地阈值规则文件"""
        rules = self._load_threshold_rules()
        if rules is not None:
            self.threshold_rules = rules
            # 重建UI中的规则行
            for _, _, row_frame in self.threshold_entries:
                row_frame.destroy()
            self.threshold_entries.clear()

            # 找到阈值面板并添加新行
            for w in self.root.winfo_children():
                if isinstance(w, ttk.LabelFrame) and '阈值规则' in (w.cget('text') or ''):
                    for rule_len, rule_threshold in rules:
                        self._add_threshold_row(w, rule_len, rule_threshold)
                    break

    @staticmethod
    def _load_threshold_rules():
        """从本地JSON文件加载阈值规则，失败返回None"""
        if not os.path.exists(ANOMALY3_RULES_FILE):
            return None
        try:
            with open(ANOMALY3_RULES_FILE, 'r', encoding='utf-8') as f:
                rules = json.load(f)
            # 验证格式
            valid = []
            for r in rules:
                if isinstance(r, list) and len(r) == 2:
                    valid.append((int(r[0]), int(r[1])))
            valid.sort(key=lambda x: x[0])
            return valid if valid else None
        except Exception:
            return None

    # ==================== 文件操作 ====================

    def _select_file(self):
        path = filedialog.askopenfilename(
            title='选择数据文件',
            filetypes=[('Excel 文件', '*.xlsx *.xls'), ('CSV 文件', '*.csv'), ('所有文件', '*.*')]
        )
        if path:
            self.filepath.set(path)
            self._log(f'已选择数据文件: {path}')

    def _load_sn_rules(self):
        """加载并解析SN规则文件（含第二sheet检验项目列表）"""
        path = filedialog.askopenfilename(
            title='选择 SN 规则文件',
            filetypes=[('Excel 文件', '*.xlsx *.xls'), ('CSV 文件', '*.csv'), ('所有文件', '*.*')]
        )
        if not path:
            return
        self.rulepath.set(path)
        try:
            if path.endswith('.csv'):
                df = pd.read_csv(path)
            else:
                df = pd.read_excel(path, sheet_name=0)  # 第一sheet: 规则

            # 尝试加载第二sheet: 检验项目列表
            self.inspection_items = []
            if not path.endswith('.csv'):
                try:
                    xl = pd.ExcelFile(path)
                    if len(xl.sheet_names) >= 2:
                        items_df = pd.read_excel(path, sheet_name=1)
                        # 自动检测列名：找"检验项目"列
                        item_col_sheet = None
                        for col in items_df.columns:
                            if '检验项目' in str(col):
                                item_col_sheet = col
                                break
                        if item_col_sheet is None and len(items_df.columns) >= 1:
                            item_col_sheet = items_df.columns[0]  # 尝试第一列
                        if item_col_sheet:
                            self.inspection_items = [
                                str(i).strip() for i in items_df[item_col_sheet].dropna().tolist()
                                if str(i).strip() and str(i).strip().lower() != 'nan'
                            ]
                        self._log(f'从SN规则第二sheet加载了 {len(self.inspection_items)} 条检验项目')
                        self._refresh_inspection_list()
                except Exception as e:
                    self._log(f'加载第二sheet检验项目列表失败（非致命）: {e}')

            self.rules = parse_sn_rules(df)
            group_info = self.rules['group_info']

            destructive_count = sum(1 for info in group_info.values() if info['has_destructive'])
            cross_count = sum(1 for info in group_info.values() if info['cross_forbidden'])

            self.sn_rules_status.set(
                f'{self.rules["group_count"]}个分组, '
                f'{destructive_count}组破坏性测试, '
                f'{cross_count}组不同工站'
            )
            self._log(f'已加载SN规则: {self.rules["group_count"]}个工站分组')
            for gid, info in group_info.items():
                sts = ', '.join(info['stations'])
                parts = []
                if info['has_destructive']:
                    parts.append(f'破坏性测试: {", ".join(sorted(info["destructive_items"])) if info["destructive_items"] else "(见规则文本)"}')
                if info['cross_forbidden']:
                    excl = f' [排除: {", ".join(sorted(info["excluded_items"]))}]' if info['excluded_items'] else ''
                    parts.append(f'不同工站{excl}')
                if info['cross_except_groups']:
                    parts.append(f'例外跨站→{", ".join(info["cross_except_groups"])}')
                if info.get('sn_shared_items'):
                    parts.append(f'SN可共用: {", ".join(sorted(info["sn_shared_items"]))}')
                if info.get('sn_exclude_items'):
                    parts.append(f'排除项: {", ".join(sorted(info["sn_exclude_items"]))}')
                if info.get('sn_not_shared_items'):
                    parts.append(f'SN不共用: {", ".join(sorted(info["sn_not_shared_items"]))}')
                if parts:
                    self._log(f'  组{gid}[{sts}]: {" | ".join(parts)}')
        except Exception as e:
            self._log(f'加载SN规则失败: {e}')
            import traceback
            traceback.print_exc()

    def _log(self, msg):
        timestamp = datetime.now().strftime('%H:%M:%S')
        self.log_text.insert(tk.END, f'[{timestamp}] {msg}\n')
        self.log_text.see(tk.END)

    # ==================== 数据分析入口 ====================

    def _start_analysis(self):
        path = self.filepath.get()
        if not path:
            messagebox.showwarning('提示', '请先选择数据文件')
            return
        if not os.path.exists(path):
            messagebox.showerror('错误', f'文件不存在: {path}')
            return

        rule_path = self.rulepath.get()
        # SN规则文件为可选：不选则跳过异常1和异常2
        has_rules = bool(rule_path and os.path.exists(rule_path))

        # 如果提供了SN规则文件，则加载
        if has_rules and self.rules is None:
            try:
                if rule_path.endswith('.csv'):
                    rules_df = pd.read_csv(rule_path)
                else:
                    rules_df = pd.read_excel(rule_path)
                self.rules = parse_sn_rules(rules_df)
            except Exception as e:
                self._log(f'加载SN规则失败: {e}')
                self.root.after(0, lambda: self.status_text.set(f'SN规则加载失败: {e}'))
                return

        has_rules = self.rules is not None

        required_cols = {
            'task': self.col_task.get().strip(),
            'item': self.col_item.get().strip(),
            'content': self.col_content.get().strip(),
            'person': self.col_person.get().strip(),
            'value': self.col_value.get().strip(),
            'sn': self.col_sn.get().strip(),
            'item_type': self.col_item_type.get().strip(),
            'station': self.col_station.get().strip(),
        }

        # 判断最小值/最大值列为可选
        spec_min_col = self.col_spec_min.get().strip()
        spec_max_col = self.col_spec_max.get().strip()
        has_spec = bool(spec_min_col and spec_max_col)

        skip_ok = self.skip_ok.get()

        self._report_progress('正在加载数据... 0%', 0)
        self._log('开始分析...')

        def _run():
            try:
                self._ui_post(lambda: self._report_progress('正在加载数据... 10%', 10))
                self.df = self._load_data(path)
                self._ui_post(lambda: self._report_progress('正在校验列名... 20%', 20))

                missing = [col for col in required_cols.values() if col and col not in self.df.columns]
                if missing:
                    self._ui_post(lambda: messagebox.showerror(
                        '列名错误',
                        f'Excel 中未找到以下列: {", ".join(missing)}\n'
                        f'找到的列: {", ".join(self.df.columns.tolist())}'
                    ))
                    self._ui_post(lambda: self.status_text.set('分析失败 - 列名不匹配'))
                    return

                # 验证判断最小值/最大值列（可选）
                actual_spec_min = spec_min_col if spec_min_col in self.df.columns else None
                actual_spec_max = spec_max_col if spec_max_col in self.df.columns else None
                has_spec = actual_spec_min is not None and actual_spec_max is not None
                if spec_min_col and spec_max_col and not has_spec:
                    self._ui_log(f'注意: 判断最小值/最大值列不存在，异常4将仅使用统计方法')

                self._ui_log(f'共加载 {len(self.df)} 行数据')

                self._ui_post(lambda: self._report_progress('正在处理数据... 25%', 25))
                self.df['_num_value'] = _to_numeric_series(self.df[required_cols['value']])

                result_col = self.col_result.get().strip()
                if skip_ok and result_col and result_col in self.df.columns:
                    before = len(self.df)
                    self.df = self.df[self.df[result_col].astype(str).str.strip() == 'OK'].copy()
                    self._ui_log(f'仅保留结果=OK的行（列: {result_col}）：{before} -> {len(self.df)}')

                self.anomalies = []
                counts = {}

                # 计算总步数用于百分比
                total_steps = 7 if has_rules else 5
                step = 0

                if has_rules:
                    step += 1
                    self._ui_log(f'正在进行异常{step}：破坏性测试共用SN...')
                    self._ui_post(lambda s=step, t=total_steps: self._report_progress(
                        f'异常检测中... {s}/{t} ({s * 100 // t}%)', s * 100 // t))
                    r1 = self._check_destructive_sn(required_cols)
                    counts['SN共用-破坏性测试'] = len(r1)
                    self.anomalies.extend(r1)

                    step += 1
                    self._ui_log(f'正在进行异常{step}：不同工站共用SN...')
                    self._ui_post(lambda s=step, t=total_steps: self._report_progress(
                        f'异常检测中... {s}/{t} ({s * 100 // t}%)', s * 100 // t))
                    r2 = self._check_cross_station_sn(required_cols)
                    counts['SN共用-不同工站'] = len(r2)
                    self.anomalies.extend(r2)
                else:
                    self._ui_log('未加载SN规则文件，跳过异常1和异常2')
                    counts['SN共用-破坏性测试'] = 0
                    counts['SN共用-不同工站'] = 0

                step += 1
                self._ui_log(f'正在进行异常{step}：不同任务单测试值一致...')
                self._ui_post(lambda s=step, t=total_steps: self._report_progress(
                    f'异常检测中... {s}/{t} ({s * 100 // t}%)', s * 100 // t))
                r3 = self._check_task_value_consistency(required_cols)
                counts['数据异常-不同任务单测试值一致'] = len(r3)
                self.anomalies.extend(r3)

                step += 1
                self._ui_log(f'正在进行异常{step}：不同人员数据分布不一致...')
                self._ui_post(lambda s=step, t=total_steps: self._report_progress(
                    f'异常检测中... {s}/{t} ({s * 100 // t}%)', s * 100 // t))
                r4 = self._check_person_distribution(required_cols, actual_spec_min, actual_spec_max)
                counts['数据异常-不同人员数据分布不一致'] = len(r4)
                self.anomalies.extend(r4)

                step += 1
                self._ui_log(f'正在进行异常{step}：测试数据规律性分布...')
                self._ui_post(lambda s=step, t=total_steps: self._report_progress(
                    f'异常检测中... {s}/{t} ({s * 100 // t}%)', s * 100 // t))
                r5 = self._check_pattern_distribution(required_cols)
                counts['数据异常-测试数据规律性分布'] = len(r5)
                self.anomalies.extend(r5)

                step += 1
                self._ui_log(f'正在进行异常{step}：人员连续出现...')
                self._ui_post(lambda s=step, t=total_steps: self._report_progress(
                    f'异常检测中... {s}/{t} ({s * 100 // t}%)', s * 100 // t))
                r6 = self._check_person_consecutive(required_cols)
                counts['数据异常-人员连续出现'] = len(r6)
                self.anomalies.extend(r6)

                step += 1
                self._ui_log(f'正在进行异常{step}：计量型测试值为空...')
                self._ui_post(lambda s=step, t=total_steps: self._report_progress(
                    f'异常检测中... {s}/{t} ({s * 100 // t}%)', s * 100 // t))
                r7 = self._check_empty_measurement_value(
                    required_cols, actual_spec_min, actual_spec_max,
                    result_col=self.col_result.get().strip() or None)
                counts['数据异常-计量型测试值为空'] = len(r7)
                self.anomalies.extend(r7)

                self._ui_log(f'分析完成：' + ', '.join(f'{k}: {v}条' for k, v in counts.items()))
                self._ui_post(self._refresh_tree)
                self._ui_post(lambda: self._report_progress(
                    f'分析完成 - 共 {len(self.anomalies)} 条异常记录', 100
                ))
            except Exception as e:
                self._ui_log(f'分析出错: {e}')
                self._ui_post(lambda: self.status_text.set(f'分析失败: {e}'))
                import traceback
                traceback.print_exc()

        threading.Thread(target=_run, daemon=True).start()

    @staticmethod
    def _load_data(path):
        if path.endswith('.csv'):
            return pd.read_csv(path)
        elif path.endswith('.xls'):
            return pd.read_excel(path, engine='xlrd')
        else:
            # 优先使用 calamine（Rust 实现，读取 .xlsx 远快于 openpyxl），
            # 未安装时回退到 openpyxl
            try:
                import python_calamine  # noqa: F401
                return pd.read_excel(path, engine='calamine')
            except (ImportError, ValueError):
                return pd.read_excel(path, engine='openpyxl')

    # ==================== 异常1：破坏性测试共用SN ====================

    def _check_destructive_sn(self, cols):
        """
        异常1：破坏性测试不允许共用SN。

        核心语义：
        - SN检测项不共用 列出的是一个互斥组，组内任意两项之间都不能共用SN
        - 即：同一个SN不能同时出现在互斥组的不同检测项中
        - 同时，同一个检测项内SN也不能重复（旧格式兼容）

        逻辑：
        1. 遍历检测类型="破坏性测试"的工站分组
        2. 确定要检查的检测项：
           - SN检测项不共用 有值 → 跨项互斥检查 + 项内复用检查
           - SN检测项不共用 为空 → 检查该工站所有检测项（项内复用）
        3. SN检测项可共用（不带!）→ 排除，不检查
        4. SN检测项可共用（带!）→ 排除项，跳过涉及这些项的情况
        """
        results = []
        if not self.rules:
            return results

        group_info = self.rules['group_info']

        sn_col = cols['sn']
        station_col = cols['station']
        task_col = cols['task']
        item_col = cols['item']
        content_col = cols['content']

        for gid, info in group_info.items():
            if not info['has_destructive']:
                continue

            group_stations = info['stations']

            # 筛选该分组的数据
            station_mask = self.df[station_col].isin(group_stations)
            group_df = self.df[station_mask]
            if group_df.empty:
                continue

            # ---------- 确定要检查的检测项 ----------
            sn_not_shared = info.get('sn_not_shared_items', set())
            sn_shared = info.get('sn_shared_items', set())       # 豁免项（SN可共用）
            sn_exclude = info.get('sn_exclude_items', set())     # 排除项（带!的）

            if sn_not_shared:
                # --- 新格式：SN检测项不共用 是一个互斥组 ---
                # 1) 跨项互斥检查：同一个SN不得同时用于互斥组内的不同项目
                # 收集所有匹配 sn_not_shared 中任一项的数据行
                cross_mask = pd.Series(False, index=group_df.index)
                for ns_item in sn_not_shared:
                    cross_mask = cross_mask | (
                        group_df[content_col].astype(str).str.contains(ns_item, na=False, regex=False) |
                        group_df[item_col].astype(str).str.contains(ns_item, na=False, regex=False)
                    )
                ns_df = group_df[cross_mask]

                if len(ns_df) >= 2:
                    # 向量化：为每个SN收集其匹配的互斥项（替代逐行 apply）
                    sn_to_group = {sn: g for sn, g in ns_df.groupby(sn_col)}
                    sn_to_ns = {}
                    for ns_item in sn_not_shared:
                        match_mask = (
                            ns_df[item_col].astype(str).str.contains(ns_item, na=False, regex=False) |
                            ns_df[content_col].astype(str).str.contains(ns_item, na=False, regex=False)
                        )
                        for sn in ns_df.loc[match_mask, sn_col].dropna().unique():
                            sn_to_ns.setdefault(sn, set()).add(ns_item)

                    for sn, sn_group in sn_to_group.items():
                        # 收集该SN涉及的所有不共用项
                        all_ns_items = sn_to_ns.get(sn, set())

                        # 过滤掉排除项
                        if sn_exclude:
                            contents_involved = set(sn_group[content_col].dropna().astype(str).unique())
                            items_involved = set(sn_group[item_col].dropna().astype(str).unique())
                            all_involved = contents_involved | items_involved
                            if any(exc in inv for exc in sn_exclude for inv in all_involved):
                                continue

                        # 如果该SN涉及多个不同的不共用项 → 异常
                        actual_ns_items = all_ns_items & sn_not_shared
                        if len(actual_ns_items) > 1:
                            tasks = sn_group[task_col].unique().tolist()
                            items = sn_group[item_col].unique().tolist()
                            contents = sn_group[content_col].unique().tolist()
                            stations_involved = sn_group[station_col].unique().tolist()

                            results.append({
                                '异常类型': 'SN共用-破坏性测试',
                                '检验项目/SN': f'SN: {str(sn)}',
                                '检验人/站点': f'站点: {", ".join(stations_involved)}',
                                '任务单/统计信息': f'任务单: {", ".join(tasks)}',
                                '详情': (
                                    f'互斥组SN复用: SN同时用于{", ".join(sorted(actual_ns_items))}, '
                                    f'共{len(sn_group)}次, '
                                    f'涉及项目: {", ".join(items)[:80]}'
                                ),
                                '备注': f'规则: {", ".join(sorted(sn_not_shared))} 之间不允许共用SN',
                                '_full_info': {
                                    'SN': str(sn),
                                    '互斥组项': sorted(actual_ns_items),
                                    '全部不共用项': sorted(sn_not_shared),
                                    '检测项目': items,
                                    '检验内容': contents,
                                    '适用站点': stations_involved,
                                    '工站分组': group_stations,
                                    '任务单': tasks,
                                    '出现次数': len(sn_group),
                                }
                            })

                    # 2) 项内复用检查：同一个项内SN是否重复出现
                    for d_item in sn_not_shared:
                        item_mask = (
                            group_df[item_col].astype(str).str.contains(d_item, na=False, regex=False) |
                            group_df[content_col].astype(str).str.contains(d_item, na=False, regex=False)
                        )
                        single_df = group_df[item_mask]
                        if len(single_df) < 2:
                            continue

                        sn_groups_inner = single_df.groupby(sn_col)
                        for sn, sn_group in sn_groups_inner:
                            if len(sn_group) < 2:
                                continue
                            # 检查是否包含排除项
                            contents_involved = set(sn_group[content_col].dropna().astype(str).unique())
                            items_involved = set(sn_group[item_col].dropna().astype(str).unique())
                            all_involved = contents_involved | items_involved
                            if sn_exclude and any(
                                exc in inv for exc in sn_exclude for inv in all_involved
                            ):
                                continue

                            tasks = sn_group[task_col].unique().tolist()
                            items = sn_group[item_col].unique().tolist()
                            contents = sn_group[content_col].unique().tolist()
                            stations_involved = sn_group[station_col].unique().tolist()

                            results.append({
                                '异常类型': 'SN共用-破坏性测试',
                                '检验项目/SN': f'SN: {str(sn)}',
                                '检验人/站点': f'站点: {", ".join(stations_involved)}',
                                '任务单/统计信息': f'任务单: {", ".join(tasks)}',
                                '详情': (
                                    f'破坏性测试项"{d_item}"中SN复用{len(sn_group)}次, '
                                    f'涉及项目: {", ".join(items)[:80]}'
                                ),
                                '备注': f'规则: {d_item} 不允许共用SN',
                                '_full_info': {
                                    'SN': str(sn),
                                    '破坏性检测项': d_item,
                                    '检测项目': items,
                                    '检验内容': contents,
                                    '适用站点': stations_involved,
                                    '工站分组': group_stations,
                                    '任务单': tasks,
                                    '出现次数': len(sn_group),
                                }
                            })

            else:
                # --- 旧格式：sn_not_shared 为空，检查工站所有检测项 ---
                all_items_in_group = set(group_df[content_col].dropna().astype(str).unique())
                all_items_in_group |= set(group_df[item_col].dropna().astype(str).unique())
                remaining = all_items_in_group - sn_shared
                check_items = sorted(remaining)
                if not check_items:
                    continue

                for d_item in check_items:
                    item_mask = (
                        group_df[item_col].astype(str).str.contains(d_item, na=False, regex=False) |
                        group_df[content_col].astype(str).str.contains(d_item, na=False, regex=False)
                    )
                    destructive_df = group_df[item_mask]
                    if len(destructive_df) < 2:
                        continue

                    if d_item in sn_shared:
                        continue

                    sn_groups = destructive_df.groupby(sn_col)
                    for sn, sn_group in sn_groups:
                        if len(sn_group) < 2:
                            continue

                        contents_involved = set(sn_group[content_col].dropna().astype(str).unique())
                        items_involved = set(sn_group[item_col].dropna().astype(str).unique())
                        all_involved = contents_involved | items_involved
                        if sn_exclude and any(
                            exc in inv for exc in sn_exclude for inv in all_involved
                        ):
                            continue

                        tasks = sn_group[task_col].unique().tolist()
                        items = sn_group[item_col].unique().tolist()
                        contents = sn_group[content_col].unique().tolist()
                        stations_involved = sn_group[station_col].unique().tolist()

                        results.append({
                            '异常类型': 'SN共用-破坏性测试',
                            '检验项目/SN': f'SN: {str(sn)}',
                            '检验人/站点': f'站点: {", ".join(stations_involved)}',
                            '任务单/统计信息': f'任务单: {", ".join(tasks)}',
                            '详情': (
                                f'破坏性测试项"{d_item}"中SN复用{len(sn_group)}次, '
                                f'涉及项目: {", ".join(items)[:80]}'
                            ),
                            '备注': f'规则: {d_item} 不允许共用SN',
                            '_full_info': {
                                'SN': str(sn),
                                '破坏性检测项': d_item,
                                '检测项目': items,
                                '检验内容': contents,
                                '适用站点': stations_involved,
                                '工站分组': group_stations,
                                '任务单': tasks,
                                '出现次数': len(sn_group),
                            }
                        })

        return results

    # ==================== 异常2：不同工站共用SN ====================

    def _check_cross_station_sn(self, cols):
        """
        异常2：不同工站不允许共用SN。

        逻辑：
        1. 从SN规则中找出所有检测类型="不同工站"的工站分组
           - 同一行工站用逗号分割 → 这些工站SN可互相共用
        2. 对每个分组，从原数据中收集其所有SN（排除"排除检测项"）
        3. 检查这些SN是否出现在原数据的**任何**其他工站中（不限于规则站点）
        4. 如果出现，且不在豁免范围内，则标记为异常
           豁免优先级：SN不共用 > SN可共用 > cross_except规则
        """
        results = []
        if not self.rules:
            return results

        group_info = self.rules['group_info']

        sn_col = cols['sn']
        station_col = cols['station']
        task_col = cols['task']
        item_col = cols['item']
        content_col = cols['content']
        item_type_col = cols['item_type']

        # ---------- 步骤1：收集"不同工站"规则的分组（排除"随机取料"） ----------
        cross_groups = {}
        for gid, info in group_info.items():
            if not info['cross_forbidden']:
                continue

            req_text = '；'.join(info['cross_req_texts'] + info['destructive_req_texts'])
            if '随机取料' in req_text:
                continue

            cross_groups[gid] = info

        if not cross_groups:
            return results

        # ---------- 步骤2：对每个分组，收集其SN并检查是否出现在其他工站 ----------
        all_stations_in_data = set(self.df[station_col].dropna().unique())
        reported_sns = set()  # 避免重复报告同一个SN

        # 预计算：只关心出现在多个工站的SN（单工站SN不可能跨站），
        # 并对其建立一次性索引，避免逐SN全表扫描（O(N^2) -> O(N)）
        station_count_per_sn = self.df.groupby(sn_col)[station_col].nunique()
        multi_station_sns = set(station_count_per_sn[station_count_per_sn > 1].index)
        sn_lookup = {}
        if multi_station_sns:
            multi_df = self.df[self.df[sn_col].isin(multi_station_sns)]
            sn_lookup = {sn: g for sn, g in multi_df.groupby(sn_col)}

        for gid, info in cross_groups.items():
            group_stations = [s for s in info['stations'] if s in all_stations_in_data]
            if not group_stations:
                continue

            # 构建该分组数据的掩码（排除"排除检测项"）
            station_mask = self.df[station_col].isin(group_stations)

            # 如果 SN检测项不共用 有值 → 只检查这些检测项
            sn_not_shared = info.get('sn_not_shared_items', set())
            if sn_not_shared:
                not_shared_mask = pd.Series(False, index=self.df.index)
                for ns_item in sn_not_shared:
                    not_shared_mask = not_shared_mask | (
                        self.df[item_col].astype(str).str.contains(ns_item, na=False, regex=False) |
                        self.df[content_col].astype(str).str.contains(ns_item, na=False, regex=False)
                    )
                station_mask = station_mask & not_shared_mask

            for exc_item in info['excluded_items']:
                exclude_mask = (
                    self.df[item_col].astype(str).str.contains(exc_item, na=False, regex=False) |
                    self.df[content_col].astype(str).str.contains(exc_item, na=False, regex=False)
                )
                if item_type_col in self.df.columns:
                    exclude_mask = exclude_mask | self.df[item_type_col].astype(str).str.contains(
                        exc_item, na=False, regex=False)
                station_mask = station_mask & ~exclude_mask

            group_df = self.df[station_mask]
            group_sns = set(group_df[sn_col].dropna().unique())
            group_sns &= multi_station_sns
            if not group_sns:
                continue

            # ---------- 步骤3：逐个SN检查 ----------
            for sn in group_sns:
                if sn in reported_sns:
                    continue

                sn_data = sn_lookup[sn]
                sn_all_stations = set(sn_data[station_col].dropna().unique())

                # 该SN出现在哪些非本组的工站中
                other_stations = sn_all_stations - set(group_stations)
                if not other_stations:
                    continue

                # ---------- 步骤4：检查每个跨站目标是否被豁免 ----------
                other_rows = sn_data[sn_data[station_col].isin(other_stations)]
                other_items = set(other_rows[item_col].astype(str).unique())
                other_contents = set(other_rows[content_col].astype(str).unique())
                other_item_types = set()
                if item_type_col in other_rows.columns:
                    other_item_types = set(other_rows[item_type_col].astype(str).unique())
                target_items = other_items | other_contents | other_item_types

                # 逐个检查其他站点
                violating_stations = []
                for other_st in sorted(other_stations):
                    is_exempt = self._check_station_exempt(
                        other_st, target_items, info
                    )
                    if not is_exempt:
                        violating_stations.append(other_st)

                if not violating_stations:
                    continue

                reported_sns.add(sn)

                tasks = sn_data[task_col].dropna().unique().tolist()
                items = sn_data[item_col].dropna().unique().tolist()

                results.append({
                    '异常类型': 'SN共用-不同工站',
                    '检验项目/SN': f'SN: {str(sn)}',
                    '检验人/站点': f'源: {", ".join(group_stations)} → 跨站: {", ".join(violating_stations)}',
                    '任务单/统计信息': f'任务单: {", ".join(tasks)}',
                    '详情': (
                        f'规则站点({", ".join(group_stations)})的SN出现在'
                        f'其他站点({", ".join(violating_stations)})'
                    ),
                    '备注': f'项目: {", ".join(items)[:100]}',
                    '_full_info': {
                        'SN': str(sn),
                        '源站点组': group_stations,
                        '违规跨站站点': violating_stations,
                        '所有跨站站点': sorted(other_stations),
                        '检验项目': items,
                        '任务单': tasks,
                        '出现次数': len(sn_data),
                    }
                })

        return results

    @staticmethod
    def _check_station_exempt(target_station, target_items, source_group_info):
        """
        检查 SN 从 source 组跨站到 target_station 是否被 source 组规则豁免。

        参数：
          target_station:   目标工站名
          target_items:     目标工站中该 SN 涉及的检测项集合
          source_group_info: 来源分组的 info dict

        豁免优先级（从高到低）：
        1. SN不共用 检测项 → 永不豁免（必须报异常）
        2. 排除项（!前缀）→ 匹配时永不豁免
        3. SN可共用 检测项 → 直接豁免
        4. cross_except_groups/items → 规则文本中的豁免
        """
        # 1. 检查 SN不共用：目标检测项匹配 → 永不豁免
        sn_not_shared = source_group_info.get('sn_not_shared_items', set())
        if sn_not_shared:
            if any(ns in ti for ns in sn_not_shared for ti in target_items):
                return False

        # 2. 检查排除项（带!前缀）：目标检测项匹配 → 永不豁免
        sn_exclude = source_group_info.get('sn_exclude_items', set())
        if sn_exclude:
            if any(se in ti for se in sn_exclude for ti in target_items):
                return False

        # 3. 检查 SN可共用：目标检测项匹配 → 直接豁免
        sn_shared = source_group_info.get('sn_shared_items', set())
        if sn_shared:
            if any(ss in ti for ss in sn_shared for ti in target_items):
                return True

        # 3. 检查规则文本中的豁免（cross_except_groups / cross_except_items）
        except_groups = source_group_info.get('cross_except_groups', set())
        except_items = source_group_info.get('cross_except_items', set())

        if not except_groups:
            return False

        # 目标站点必须在豁免列表中
        if not any(eg in target_station for eg in except_groups):
            return False

        # 如果指定了豁免检测项，则目标检测项必须匹配
        if except_items:
            return any(ei in ti for ei in except_items for ti in target_items)

        # 无检测项限制 → 完全豁免
        return True

    # ==================== 异常3：不同任务单测试值一致 ====================

    def _check_task_value_consistency(self, cols):
        """
        异常3：不同任务单，相同检验项目+检验内容，测试值存在高度一致性。

        检测方式：分别排序后，按位置依次对比。
        阈值规则：
        - 4个值以上 → 至少3个位置值相同
        - 6个值以上 → 至少4个位置值相同
        - 少于4个值 → 必须全部位置相同
        """
        results = []
        task_col = cols['task']
        item_col = cols['item']
        content_col = cols['content']
        person_col = cols['person']

        # 预计算阈值规则（降序）并缓存，避免在每对任务比较时重复排序
        sorted_rules = sorted(self.threshold_rules, key=lambda x: x[0], reverse=True)
        _threshold_cache = {}

        def _threshold(compare_len):
            t = _threshold_cache.get(compare_len)
            if t is None:
                t = compare_len
                for rule_len, rule_threshold in sorted_rules:
                    if compare_len >= rule_len:
                        t = min(rule_threshold, compare_len)
                        break
                _threshold_cache[compare_len] = t
            return t

        groups = self.df.groupby([item_col, content_col])

        for (item, content), group in groups:
            task_groups = group.groupby(task_col)
            if len(task_groups) < 2:
                continue

            task_values = {}   # task -> 排序后的 Python 列表（用于展示）
            task_arrays = {}   # task -> 排序后的 numpy 数组（用于向量化对比）
            task_persons = {}
            for task, task_df in task_groups:
                vals = task_df['_num_value'].to_numpy(dtype=float)
                vals = vals[~np.isnan(vals)]
                if vals.size == 0:
                    continue
                vals.sort()
                task_values[task] = vals.tolist()
                task_arrays[task] = vals
                person_arr = task_df[person_col].to_numpy()
                persons = person_arr[~pd.isna(person_arr)]
                task_persons[task] = pd.unique(persons).tolist() if persons.size else []

            if len(task_values) < 2:
                continue

            tasks = list(task_values.keys())
            seen_pairs = set()
            for i in range(len(tasks)):
                for j in range(i + 1, len(tasks)):
                    vals_i = task_values[tasks[i]]
                    vals_j = task_values[tasks[j]]

                    # 取较短的长度，按位置依次对比
                    compare_len = min(len(vals_i), len(vals_j))
                    threshold = _threshold(compare_len)

                    # 短序列用 Python 循环（小数组更快），长序列用 numpy 向量化
                    if compare_len <= 12:
                        match_count = 0
                        matched_values = []
                        for pos in range(compare_len):
                            if abs(vals_i[pos] - vals_j[pos]) < 1e-9:
                                match_count += 1
                                matched_values.append(vals_i[pos])
                    else:
                        arr_i = task_arrays[tasks[i]]
                        arr_j = task_arrays[tasks[j]]
                        match_mask = np.abs(arr_i[:compare_len] - arr_j[:compare_len]) < 1e-9
                        match_count = int(match_mask.sum())
                        matched_values = arr_i[:compare_len][match_mask].tolist() if match_count else []

                    if match_count >= threshold and match_count > 0:
                        pair_key = (min(tasks[i], tasks[j]), max(tasks[i], tasks[j]))
                        if pair_key in seen_pairs:
                            continue
                        seen_pairs.add(pair_key)

                        # 获取两个任务单各自的检验人
                        persons_i = task_persons[tasks[i]]
                        persons_j = task_persons[tasks[j]]
                        all_persons = persons_i + persons_j

                        matched_str = ','.join(str(v) for v in matched_values)
                        display_matched = matched_str if len(matched_str) <= 80 else matched_str[:77] + '...'

                        results.append({
                            '异常类型': '数据异常-不同任务单测试值一致',
                            '检验项目/SN': str(item),
                            '检验人/站点': f'检验人: {", ".join(all_persons)}',
                            '任务单/统计信息': f'{str(tasks[i])} vs {str(tasks[j])}',
                            '详情': (
                                f'排序后按位对比: {match_count}/{compare_len}个位置相同'
                                f'(阈值≥{threshold}), 相同值: {display_matched}'
                            ),
                            '备注': f'检验内容: {str(content)[:60]}',
                            '_full_info': {
                                '检验项目': str(item),
                                '检验内容': str(content),
                                '检验人': ', '.join(all_persons),
                                '任务单A': str(tasks[i]),
                                '任务单B': str(tasks[j]),
                                'A排序值': ','.join(str(v) for v in task_values[tasks[i]]),
                                'B排序值': ','.join(str(v) for v in task_values[tasks[j]]),
                                '对比长度': compare_len,
                                '相同位置数': match_count,
                                '阈值': threshold,
                            }
                        })

        return results

    # ==================== 异常4：不同检验人数据分布不一致 ====================

    def _check_person_distribution(self, cols, spec_min_col=None, spec_max_col=None):
        """
        异常4：不同检验人，相同检验项目+检验内容，数据分布应在同一区间。

        检测逻辑（按优先级）：
        1. 规格范围对比：用判断最小值/最大值作为规格范围，
           检测各人测量值是否在规格范围内，以及不同人之间在规格范围内数据的分布差异。
        2. Z-score检测：均值离群的检验人（z > 2.0）。
        3. IQR范围对比：所有人的数据范围应重叠。
        """
        results = []
        has_spec = spec_min_col is not None and spec_max_col is not None
        item_col = cols['item']
        content_col = cols['content']
        person_col = cols['person']

        # 构建规格列数值（如果存在）
        if has_spec:
            self.df['_spec_min'] = _to_numeric_series(self.df[spec_min_col])
            self.df['_spec_max'] = _to_numeric_series(self.df[spec_max_col])
            # 标记有规格限的行
            has_spec_mask = (
                self.df['_spec_min'].notna() & self.df['_spec_max'].notna()
            )
        else:
            has_spec_mask = pd.Series(False, index=self.df.index)

        groups = self.df.groupby([item_col, content_col])

        for (item, content), group in groups:
            # ========== 检测1：规格范围对比 ==========
            if has_spec:
                spec_results = self._check_spec_range(
                    group, item, content, item_col, content_col, person_col,
                    has_spec_mask[group.index]
                )
                results.extend(spec_results)

            # ========== 检测2&3：统计方法（Z-score + IQR范围对比）==========
            person_values = {}
            for person, person_df in group.groupby(person_col):
                clean_vals = person_df['_num_value'].dropna().tolist()
                if len(clean_vals) >= 5:
                    person_values[person] = clean_vals

            if len(person_values) < 2:
                continue

            person_stats = {}
            all_vals_pooled = []
            for person, vals in person_values.items():
                all_vals_pooled.extend(vals)
                person_stats[person] = {
                    'mean': statistics.mean(vals),
                    'std': statistics.stdev(vals) if len(vals) > 1 else 0,
                    'count': len(vals),
                    'min': min(vals),
                    'max': max(vals),
                    'median': statistics.median(vals),
                }

            all_means = [s['mean'] for s in person_stats.values()]

            # --- Z-score 均值离群 ---
            overall_mean = statistics.mean(all_means)
            overall_std = statistics.stdev(all_means) if len(all_means) > 1 else 0

            if overall_std >= 0.001:
                for person, stats in person_stats.items():
                    if overall_std == 0:
                        continue
                    z_score = abs(stats['mean'] - overall_mean) / overall_std
                    if z_score > 2.0:
                        range_summary = self._build_range_summary(person_stats, person)
                        results.append({
                            '异常类型': '数据异常-不同人员数据分布不一致',
                            '检验项目/SN': str(item),
                            '检验人/站点': f'异常检验人: {str(person)}',
                            '任务单/统计信息': (
                                f'均值={stats["mean"]:.4f} '
                                f'(整体={overall_mean:.4f}, Z={z_score:.2f})'
                            ),
                            '详情': (
                                f'Z-score检测: 该人均值{stats["mean"]:.4f}偏离整体{overall_mean:.4f}, '
                                f'范围[{stats["min"]:.4f}, {stats["max"]:.4f}], '
                                f'n={stats["count"]}'
                            ),
                            '备注': f'检验内容: {str(content)[:60]}',
                            '_full_info': {
                                '检测方法': 'Z-score均值离群检测',
                                '检验项目': str(item),
                                '检验内容': str(content),
                                '异常检验人': str(person),
                                '该人均值': stats['mean'],
                                '该人标准差': stats['std'],
                                '该人最小值': stats['min'],
                                '该人最大值': stats['max'],
                                '该人数据量': stats['count'],
                                '整体均值': overall_mean,
                                '整体标准差': overall_std,
                                'Z-score': z_score,
                                '所有人员均值': {p: s['mean'] for p, s in person_stats.items()},
                                '所有人员范围': range_summary,
                                '_person_stats_table': self._build_person_stats_table(person_stats, person),
                            }
                        })

            # --- 两两不重叠检测：某人数据范围与其余人完全不重叠 ---
            if len(person_stats) >= 2:
                # 对每个人，计算"其余所有人合并"的范围
                for person, stats in person_stats.items():
                    other_mins = []
                    other_maxes = []
                    other_vals = []
                    for op, os_stats in person_stats.items():
                        if op != person:
                            other_mins.append(os_stats['min'])
                            other_maxes.append(os_stats['max'])
                            other_vals.extend(person_values[op])
                    if not other_vals:
                        continue

                    other_min = min(other_mins)
                    other_max = max(other_maxes)

                    # 此人与其余人的范围完全不重叠
                    if stats['max'] < other_min:
                        reason = (
                            f'范围完全不重叠: 此人范围[{stats["min"]:.4f}, {stats["max"]:.4f}] '
                            f'全部低于其余人[{other_min:.4f}, {other_max:.4f}]'
                        )
                    elif stats['min'] > other_max:
                        reason = (
                            f'范围完全不重叠: 此人范围[{stats["min"]:.4f}, {stats["max"]:.4f}] '
                            f'全部高于其余人[{other_min:.4f}, {other_max:.4f}]'
                        )
                    else:
                        continue

                    range_summary = self._build_range_summary(person_stats, person)

                    results.append({
                        '异常类型': '数据异常-不同人员数据分布不一致',
                        '检验项目/SN': str(item),
                        '检验人/站点': f'异常检验人: {str(person)}',
                        '任务单/统计信息': (
                            f'此人范围[{stats["min"]:.4f}, {stats["max"]:.4f}], '
                            f'其余人范围[{other_min:.4f}, {other_max:.4f}]'
                        ),
                        '详情': reason,
                        '备注': f'检验内容: {str(content)[:60]}',
                        '_full_info': {
                            '检测方法': '两两范围不重叠检测',
                            '检验项目': str(item),
                            '检验内容': str(content),
                            '异常检验人': str(person),
                            '该人均值': stats['mean'],
                            '该人最小值': stats['min'],
                            '该人最大值': stats['max'],
                            '该人数据量': stats['count'],
                            '其余人合并最小值': other_min,
                            '其余人合并最大值': other_max,
                            '所有人员范围': range_summary,
                            '_person_stats_table': self._build_person_stats_table(person_stats, person),
                        }
                    })

            # --- IQR 范围对比 ---
            if len(all_vals_pooled) >= 10:
                sorted_all = sorted(all_vals_pooled)
                n_all = len(sorted_all)
                q1 = sorted_all[n_all // 4]
                q3 = sorted_all[3 * n_all // 4]
                iqr = q3 - q1

                if iqr >= 0.001:
                    lower_bound = q1 - 1.5 * iqr
                    upper_bound = q3 + 1.5 * iqr

                    for person, stats in person_stats.items():
                        p_min = stats['min']
                        p_max = stats['max']
                        p_median = stats['median']

                        is_shifted_up = p_min > q3
                        is_shifted_down = p_max < q1
                        is_median_outside = p_median < lower_bound or p_median > upper_bound

                        if is_shifted_up or is_shifted_down or is_median_outside:
                            if is_shifted_up:
                                reason = f'此人所有值均高于其他人员(Q3={q3:.4f}), 范围[{p_min:.4f}, {p_max:.4f}]'
                            elif is_shifted_down:
                                reason = f'此人所有值均低于其他人员(Q1={q1:.4f}), 范围[{p_min:.4f}, {p_max:.4f}]'
                            else:
                                reason = f'此人中位数{p_median:.4f}超出正常范围[{lower_bound:.4f}, {upper_bound:.4f}], 范围[{p_min:.4f}, {p_max:.4f}]'

                            range_summary = self._build_range_summary(person_stats, person)

                            results.append({
                                '异常类型': '数据异常-不同人员数据分布不一致',
                                '检验项目/SN': str(item),
                                '检验人/站点': f'异常检验人: {str(person)}',
                                '任务单/统计信息': (
                                    f'整体范围[{lower_bound:.4f}, {upper_bound:.4f}], '
                                    f'此人范围[{p_min:.4f}, {p_max:.4f}]'
                                ),
                                '详情': reason,
                                '备注': f'检验内容: {str(content)[:60]}',
                                '_full_info': {
                                    '检测方法': 'IQR范围对比检测',
                                    '检验项目': str(item),
                                    '检验内容': str(content),
                                    '异常检验人': str(person),
                                    '该人均值': stats['mean'],
                                    '该人中位数': stats['median'],
                                    '该人标准差': stats['std'],
                                    '该人最小值': stats['min'],
                                    '该人最大值': stats['max'],
                                    '该人数据量': stats['count'],
                                    '整体Q1': q1,
                                    '整体Q3': q3,
                                    '整体IQR': iqr,
                                    '整体正常下限': lower_bound,
                                    '整体正常上限': upper_bound,
                                    '所有人员范围': range_summary,
                                    '_person_stats_table': self._build_person_stats_table(person_stats, person),
                                }
                            })

            # --- 热点分布检测：比较各人与整体值域分布的差异 ---
            if len(person_stats) >= 2:
                hotspot_results = self._check_distribution_hotspot(
                    person_stats, all_vals_pooled, item, content,
                    person_stats_original=person_values
                )
                results.extend(hotspot_results)

        return results

    def _check_spec_range(self, group, item, content, item_col, content_col, person_col, has_spec_mask):
        """规格范围对比检测：基于判断最小值/最大值判断数据是否在规格范围内"""
        results = []
        # 获取有规格限的数据
        group_with_spec = group[has_spec_mask]
        if len(group_with_spec) < 5:
            return results

        # 收集每个人的数据
        person_data = {}
        for person, person_df in group_with_spec.groupby(person_col):
            vals = person_df['_num_value'].dropna().tolist()
            specs_min = person_df['_spec_min'].dropna().tolist()
            specs_max = person_df['_spec_max'].dropna().tolist()
            if len(vals) < 3:
                continue

            in_spec = []
            out_spec = []
            # 对每行数据，使用对应的规格限判断
            for val, smin, smax in zip(
                person_df['_num_value'],
                person_df['_spec_min'],
                person_df['_spec_max']
            ):
                if pd.isna(val):
                    continue
                if pd.notna(smin) and pd.notna(smax):
                    if smin <= val <= smax:
                        in_spec.append(val)
                    else:
                        out_spec.append((val, smin, smax))
                else:
                    in_spec.append(val)  # 无规格限的行当作在规格内

            if in_spec or out_spec:
                person_data[person] = {
                    'in_spec': in_spec,
                    'out_spec': out_spec,
                    'total': len(in_spec) + len(out_spec),
                }

        if len(person_data) < 1:
            return results

        # 构建所有人员范围摘要
        person_range_summary = {}
        for p, pd_data in person_data.items():
            all_vals_p = pd_data['in_spec'] + [v for v, _, _ in pd_data['out_spec']]
            if all_vals_p:
                person_range_summary[p] = (
                    f'在规格: {len(pd_data["in_spec"])}/{pd_data["total"]}, '
                    f'范围=[{min(all_vals_p):.4f}, {max(all_vals_p):.4f}]'
                )

        # 计算规格限中位数，供图表使用
        spec_min_median = round(group_with_spec['_spec_min'].dropna().median(), 4)
        spec_max_median = round(group_with_spec['_spec_max'].dropna().median(), 4)

        # --- 检测A：某人有大量出规格数据，而其他人没有 ---
        for person, pd_data in person_data.items():
            out_count = len(pd_data['out_spec'])
            total = pd_data['total']
            if total < 3:
                continue

            out_ratio = out_count / total

            # 计算其他人的平均出规格率
            other_ratios = []
            for op, opd in person_data.items():
                if op != person and opd['total'] >= 3:
                    other_ratios.append(len(opd['out_spec']) / opd['total'])

            avg_other_ratio = statistics.mean(other_ratios) if other_ratios else 0

            # 条件：出规格率 > 20% 且 显著高于其他人（> 平均值 + 15%）
            if out_ratio > 0.20 and out_ratio > avg_other_ratio + 0.15:
                out_details = []
                for val, smin, smax in pd_data['out_spec'][:10]:
                    reason = '低于下限' if val < smin else '高于上限'
                    out_details.append(f'值{val:.4f}{reason}(规格[{smin:.4f},{smax:.4f}])')
                out_str = '; '.join(out_details)
                if len(pd_data['out_spec']) > 10:
                    out_str += f' ... 等共{out_count}条'

                results.append({
                    '异常类型': '数据异常-不同人员数据分布不一致',
                    '检验项目/SN': str(item),
                    '检验人/站点': f'异常检验人: {str(person)}',
                    '任务单/统计信息': (
                        f'出规格率 {out_ratio:.0%}({out_count}/{total}), '
                        f'其他人平均 {avg_other_ratio:.0%}'
                    ),
                    '详情': f'规格范围对比: {out_str}',
                    '备注': f'检验内容: {str(content)[:60]}',
                    '_full_info': {
                        '检测方法': '规格范围对比-出规格率异常',
                        '检验项目': str(item),
                        '检验内容': str(content),
                        '异常检验人': str(person),
                        '该人出规格数': out_count,
                        '该人总数据量': total,
                        '该人出规格率': round(out_ratio, 4),
                        '其他人平均出规格率': round(avg_other_ratio, 4),
                        '判断最小值': spec_min_median,
                        '判断最大值': spec_max_median,
                        '出规格详情': [{'值': v, '规格下限': smin, '规格上限': smax}
                                   for v, smin, smax in pd_data['out_spec'][:20]],
                        '所有人员范围': person_range_summary,
                        '_person_stats_table': [
                            {
                                '检验人': p,
                                '数据量': len(all_vals),
                                '最小值': round(min(all_vals), 4),
                                '最大值': round(max(all_vals), 4),
                                '均值': round(statistics.mean(all_vals), 4),
                                '中位数': round(statistics.median(all_vals), 4),
                                '标准差': round(statistics.stdev(all_vals), 4) if len(all_vals) > 1 else 0,
                                '出规格率': f'{len(pd["out_spec"])}/{len(all_vals)}',
                                '备注': '← 异常' if p == person else '',
                            }
                            for p, pd in person_data.items()
                            for all_vals in [[v for v, _, _ in pd['out_spec']] + pd['in_spec']]
                            if all_vals
                        ],
                    }
                })

        # --- 检测B：比较不同人员之间的规格内数据分布 ---
        # 当某人规格内的数据范围与其他人规格内的数据范围不重叠时
        if len(person_data) >= 2:
            # 收集每个人在规格内的值的统计
            person_in_spec_stats = {}
            for p, pd_data in person_data.items():
                vals = pd_data['in_spec']
                if len(vals) >= 3:
                    person_in_spec_stats[p] = {
                        'min': min(vals),
                        'max': max(vals),
                        'mean': statistics.mean(vals),
                        'median': statistics.median(vals),
                        'count': len(vals),
                    }

            if len(person_in_spec_stats) >= 2:
                # 用所有人规格内数据计算整体范围
                all_in_spec = []
                for pd_data in person_data.values():
                    all_in_spec.extend(pd_data['in_spec'])
                if len(all_in_spec) >= 10:
                    sorted_in = sorted(all_in_spec)
                    ni = len(sorted_in)
                    qi1 = sorted_in[ni // 4]
                    qi3 = sorted_in[3 * ni // 4]
                    iiqr = qi3 - qi1

                    if iiqr >= 0.001:
                        in_lower = qi1 - 1.5 * iiqr
                        in_upper = qi3 + 1.5 * iiqr

                        for p, ps in person_in_spec_stats.items():
                            # 某人在规格内的数据全部偏离其他人
                            p_in_min = ps['min']
                            p_in_max = ps['max']

                            if p_in_min > qi3:
                                reason = f'规格内数据偏高: 此人规格内范围[{p_in_min:.4f},{p_in_max:.4f}]全部高于其他人员(Q3={qi3:.4f})'
                            elif p_in_max < qi1:
                                reason = f'规格内数据偏低: 此人规格内范围[{p_in_min:.4f},{p_in_max:.4f}]全部低于其他人员(Q1={qi1:.4f})'
                            elif ps['median'] < in_lower or ps['median'] > in_upper:
                                reason = f'规格内中位数{ps["median"]:.4f}偏离规格内正常范围[{in_lower:.4f},{in_upper:.4f}]'
                            else:
                                continue

                            results.append({
                                '异常类型': '数据异常-不同人员数据分布不一致',
                                '检验项目/SN': str(item),
                                '检验人/站点': f'异常检验人: {str(p)}',
                                '任务单/统计信息': (
                                    f'规格内正常范围[{in_lower:.4f}, {in_upper:.4f}], '
                                    f'此人规格内范围[{p_in_min:.4f}, {p_in_max:.4f}]'
                                ),
                                '详情': reason,
                                '备注': f'检验内容: {str(content)[:60]}',
                                '_full_info': {
                                    '检测方法': '规格范围对比-规格内分布差异',
                                    '检验项目': str(item),
                                    '检验内容': str(content),
                                    '异常检验人': str(p),
                                    '该人规格内均值': ps['mean'],
                                    '该人规格内中位数': ps['median'],
                                    '该人规格内最小值': ps['min'],
                                    '该人规格内最大值': ps['max'],
                                    '该人规格内数据量': ps['count'],
                                    '整体规格内Q1': qi1,
                                    '整体规格内Q3': qi3,
                                    '判断最小值': spec_min_median,
                                    '判断最大值': spec_max_median,
                                    '整体规格内IQR': iiqr,
                                    '整体规格内正常下限': in_lower,
                                    '整体规格内正常上限': in_upper,
                                    '所有人员范围': person_range_summary,
                                    '_person_stats_table': [
                                        {
                                            '检验人': inner_p,
                                            '数据量': sps['count'],
                                            '最小值': round(sps['min'], 4),
                                            '最大值': round(sps['max'], 4),
                                            '均值': round(sps['mean'], 4),
                                            '中位数': round(sps['median'], 4),
                                            '备注': '← 异常' if inner_p == p else '',
                                        }
                                        for inner_p, sps in person_in_spec_stats.items()
                                    ] if person_in_spec_stats else [],
                                }
                            })

        return results

    @staticmethod
    def _build_range_summary(person_stats, highlight_person):
        """构建所有人员数据范围摘要，用于显示和导出"""
        summary = {}
        for p, s in person_stats.items():
            marker = ' ← 异常' if p == highlight_person else ''
            summary[p] = (
                f'均值={s["mean"]:.4f}, 范围=[{s["min"]:.4f}, {s["max"]:.4f}], '
                f'n={s["count"]}{marker}'
            )
        return summary

    @staticmethod
    def _build_person_stats_table(person_stats, highlight_person):
        """构建人员分布对比表格数据，返回 list[dict]"""
        table = []
        for p, s in person_stats.items():
            table.append({
                '检验人': p,
                '数据量': s['count'],
                '最小值': round(s['min'], 4),
                '最大值': round(s['max'], 4),
                '均值': round(s['mean'], 4),
                '中位数': round(s['median'], 4),
                '标准差': round(s['std'], 4) if s['std'] else 0,
                '备注': '← 异常' if p == highlight_person else '',
            })
        return table

    # ---------- 热点分布检测辅助方法 ----------

    def _check_distribution_hotspot(self, person_stats, all_vals_pooled,
                                     item, content, person_stats_original=None):
        """
        将整体值域划分为10个区间，对比各检验人的数据分布与整体分布的差异。
        分布差异显著（JS散度 > 阈值）的检验人判定为异常。
        """
        results = []
        import math as _math

        if not all_vals_pooled or len(all_vals_pooled) < 10:
            return results

        # --- 动态确定合适的分箱数 ---
        val_min = min(all_vals_pooled)
        val_max = max(all_vals_pooled)
        val_range = val_max - val_min

        if val_range < 0.001:
            return results

        # 根据数据量和范围动态确定分箱数（5-15个）
        total_n = len(all_vals_pooled)
        bin_count = max(5, min(12, total_n // 20, int(val_range * 2) + 1))
        bin_count = max(5, min(bin_count, 15))

        # 轻微扩大范围避免边界值落在外面
        margin = val_range * 0.001
        bin_edges = [val_min - margin + (val_range + 2 * margin) * i / bin_count
                     for i in range(bin_count + 1)]

        bin_labels = []
        for i in range(bin_count):
            bin_labels.append(f'[{bin_edges[i]:.2f}, {bin_edges[i+1]:.2f})')
        # 最后一个区间包含右端点
        bin_labels[-1] = f'[{bin_edges[-2]:.2f}, {bin_edges[-1]:.2f}]'

        # --- 计算整体分布 ---
        def _bin_values(values, edges):
            counts = [0] * (len(edges) - 1)
            for v in values:
                for bi in range(len(edges) - 1):
                    if bi == len(edges) - 2:
                        if edges[bi] <= v <= edges[bi + 1]:
                            counts[bi] += 1
                            break
                    else:
                        if edges[bi] <= v < edges[bi + 1]:
                            counts[bi] += 1
                            break
            return counts

        overall_counts = _bin_values(all_vals_pooled, bin_edges)
        overall_total = len(all_vals_pooled)
        overall_props = [c / overall_total for c in overall_counts]

        # --- 计算每个人的分布 ---
        person_distributions = {}
        for person, stats in person_stats.items():
            person_vals = (person_stats_original or {}).get(person, [])
            if not person_vals and person_stats_original:
                continue
            if not person_vals:
                # 从stats重建（不准确但做个兜底）
                continue
            counts = _bin_values(person_vals, bin_edges)
            total = len(person_vals)
            props = [c / total for c in counts]
            person_distributions[person] = {
                'counts': counts,
                'props': props,
                'total': total,
            }

        if len(person_distributions) < 2:
            return results

        # --- 计算每个人的分布差异度 ---
        divergences = {}
        for person, pd_info in person_distributions.items():
            # 使用 Jensen-Shannon 散度：JS(P||Q) = (KL(P||M) + KL(Q||M)) / 2
            p = pd_info['props']
            q = overall_props

            # 平滑处理：加小值避免 log(0)
            eps = 1e-10
            p_smooth = [max(pp, eps) for pp in p]
            q_smooth = [max(qq, eps) for qq in q]
            m = [(pp + qq) / 2 for pp, qq in zip(p_smooth, q_smooth)]

            kl_pm = sum(pp * _math.log(pp / mm) for pp, mm in zip(p_smooth, m) if pp > eps)
            kl_qm = sum(qq * _math.log(qq / mm) for qq, mm in zip(q_smooth, m) if qq > eps)
            js_div = (kl_pm + kl_qm) / 2

            divergences[person] = js_div

        # --- 判断异常 ---
        div_values = list(divergences.values())
        div_mean = statistics.mean(div_values)
        div_std = statistics.stdev(div_values) if len(div_values) > 1 else 0

        # 阈值：均值 + 1.5 * std，且至少 0.15
        threshold = max(div_mean + 1.5 * div_std, 0.15)

        for person, js_div in divergences.items():
            if js_div > threshold:
                stats = person_stats[person]
                pd_info = person_distributions[person]

                # 找出差异最大的 bin
                max_diff = 0
                max_diff_bin = 0
                for bi in range(bin_count):
                    diff = abs(pd_info['props'][bi] - overall_props[bi])
                    if diff > max_diff:
                        max_diff = diff
                        max_diff_bin = bi

                # 构建分布对比表数据（用于详情图表展示）
                dist_table = []
                for bi in range(bin_count):
                    dist_table.append({
                        '区间': bin_labels[bi],
                        '整体占比': f'{overall_props[bi]:.1%}',
                        f'{str(person)}(占比)': f'{pd_info["props"][bi]:.1%}',
                        '差异': f'{abs(pd_info["props"][bi] - overall_props[bi]):.1%}',
                    })

                # 也加入其他人的分布
                dist_columns = ['区间', '整体占比']
                for p_name in person_distributions:
                    p_marker = '← 异常' if p_name == person else ''
                    dist_columns.append(f'{p_name}{p_marker}')
                dist_columns.append('')

                # 完整的横向分布表
                dist_full_table = []
                for bi in range(bin_count):
                    row = {'区间': bin_labels[bi]}
                    row['整体占比'] = f'{overall_props[bi]:.1%}'
                    for p_name in person_distributions:
                        marker = '←' if p_name == person else ''
                        row[f'{p_name}{marker}'] = f'{person_distributions[p_name]["props"][bi]:.1%}'
                    dist_full_table.append(row)

                results.append({
                    '异常类型': '数据异常-不同人员数据分布不一致',
                    '检验项目/SN': str(item),
                    '检验人/站点': f'异常检验人: {str(person)}',
                    '任务单/统计信息': (
                        f'JS散度={js_div:.4f}(阈值={threshold:.4f}), '
                        f'最大差异区间{bin_labels[max_diff_bin]}'
                    ),
                    '详情': (
                        f'热点分布不一致: 该人数据分布与整体分布JS散度={js_div:.4f}, '
                        f'最异常区间{bin_labels[max_diff_bin]}, '
                        f'整体{overall_props[max_diff_bin]:.0%} vs 该人{pd_info["props"][max_diff_bin]:.0%}'
                    ),
                    '备注': f'检验内容: {str(content)[:60]}',
                    '_full_info': {
                        '检测方法': '热点分布检测(JS散度)',
                        '检验项目': str(item),
                        '检验内容': str(content),
                        '异常检验人': str(person),
                        'JS散度值': round(js_div, 4),
                        '判定阈值': round(threshold, 4),
                        '平均散度': round(div_mean, 4),
                        '散度标准差': round(div_std, 4),
                        '最大差异区间': bin_labels[max_diff_bin],
                        '整体该区间占比': f'{overall_props[max_diff_bin]:.1%}',
                        '该人该区间占比': f'{pd_info["props"][max_diff_bin]:.1%}',
                        '该人均值': stats['mean'],
                        '该人数据量': stats['count'],
                        '分箱数': bin_count,
                        '值域范围': f'[{val_min:.4f}, {val_max:.4f}]',
                        '_distribution_chart': dist_full_table,
                        '_distribution_columns': dist_columns,
                        '_person_stats_table': self._build_person_stats_table(person_stats, person),
                    }
                })

        return results

    # ==================== 分布图绘制 ====================

    @staticmethod
    def _draw_distribution_chart(canvas):
        """在 Canvas 上绘制分组柱状图，对比各人员分布与整体分布"""
        dist_chart = getattr(canvas, '_dist_chart_data', None)
        if not dist_chart:
            return

        canvas.delete('all')
        w = canvas.winfo_width()
        h = canvas.winfo_height()
        if w < 100 or h < 80:
            return

        # 解析数据
        cols = list(dist_chart[0].keys())
        # 找到人员列（非"区间"、非"整体占比"的列）
        person_cols = [c for c in cols if c not in ('区间', '整体占比', '')]
        bin_labels = [row['区间'] for row in dist_chart]

        # 解析百分比
        def _pct(val):
            try:
                return float(str(val).rstrip('%')) / 100.0
            except (ValueError, AttributeError):
                return 0.0

        overall_vals = [_pct(row.get('整体占比', '0%')) for row in dist_chart]
        person_vals = {}
        for pc in person_cols:
            clean_name = pc.rstrip('←').rstrip(' ')
            person_vals[pc] = [_pct(row.get(pc, '0%')) for row in dist_chart]

        n_bins = len(bin_labels)
        n_groups = 1 + len(person_cols)  # 整体 + 各人员
        if n_bins == 0 or n_groups == 0:
            return

        # 配色方案
        colors = ['#5B9BD5']  # 整体：蓝色
        person_palette = ['#ED7D31', '#70AD47', '#FFC000', '#9B59B6',
                          '#E74C3C', '#3498DB', '#1ABC9C', '#E67E22']
        for i, pc in enumerate(person_cols):
            if '←' in pc:
                colors.append('#C0392B')  # 异常人员：深红色
            else:
                colors.append(person_palette[i % len(person_palette)])

        # 边距
        left_m = 70
        right_m = 20
        top_m = 30
        bottom_m = 50
        plot_w = w - left_m - right_m
        plot_h = h - top_m - bottom_m
        if plot_w < 10 or plot_h < 10:
            return

        # 计算 Y 轴刻度 (0% ~ max_val+10%)
        max_val = max(max(overall_vals), max(max(pv) for pv in person_vals.values()))
        y_max = min(1.0, max_val * 1.15 + 0.05)
        if y_max < 0.02:
            y_max = 0.1

        # 绘制 Y 轴刻度线和标签
        n_y_ticks = 5
        for i in range(n_y_ticks + 1):
            frac = i / n_y_ticks
            y = top_m + plot_h * (1 - frac)
            val = y_max * frac
            canvas.create_line(left_m - 4, y, left_m, y, fill='#666')
            canvas.create_line(left_m, y, left_m + plot_w, y, fill='#eee')
            canvas.create_text(left_m - 8, y, text=f'{val:.0%}',
                               anchor='e', font=('Arial', 8), fill='#333')

        # 绘制各组柱子
        bar_area_w = plot_w / n_bins
        group_w = bar_area_w * 0.8
        bar_w = max(2, group_w / n_groups)
        gap = (bar_area_w - group_w) / 2

        for bi in range(n_bins):
            x_start = left_m + bi * bar_area_w + gap
            for gi in range(n_groups):
                bar_x = x_start + gi * bar_w

                if gi == 0:
                    val = overall_vals[bi]
                else:
                    pc = person_cols[gi - 1]
                    val = person_vals[pc][bi]

                bar_h = (val / y_max) * plot_h if y_max > 0 else 0
                y_top = top_m + plot_h - bar_h
                y_bottom = top_m + plot_h

                # 绘制柱体
                color = colors[gi]
                if bar_h > 0.5:
                    canvas.create_rectangle(bar_x, y_top, bar_x + bar_w - 1, y_bottom,
                                            fill=color, outline='', width=0)
                # 顶端显示数值（仅值>5%的标注）
                if val > 0.05 and bar_h > 10:
                    canvas.create_text(bar_x + bar_w / 2, y_top - 8,
                                       text=f'{val:.0%}', font=('Arial', 6), fill='#333')

        # 绘制 X 轴标签（简化显示）
        label_step = max(1, n_bins // 8)
        for bi in range(0, n_bins, label_step):
            x_center = left_m + bi * bar_area_w + bar_area_w / 2
            short_label = bin_labels[bi]
            # 缩短标签：取前6字符
            if len(short_label) > 8:
                # 尝试提取 [x.xx, 格式
                import re as _re
                m = _re.match(r'\[([\d.]+),\s*([\d.]+)', short_label)
                if m:
                    short_label = f'{m.group(1)}~{m.group(2)}'
                else:
                    short_label = short_label[:6]
            canvas.create_text(x_center, top_m + plot_h + 12,
                               text=short_label, font=('Arial', 7),
                               angle=45 if n_bins > 6 else 0, anchor='n', fill='#333')

        # 绘制图例
        legend_y = top_m - 18
        legend_items = [('整体', colors[0])]
        for i, pc in enumerate(person_cols):
            clean_name = pc.rstrip('←').rstrip(' ')
            marker = ' (异常)' if '←' in pc else ''
            legend_items.append((clean_name + marker, colors[i + 1]))

        lx = left_m
        for label, color in legend_items:
            canvas.create_rectangle(lx, legend_y, lx + 10, legend_y + 10,
                                    fill=color, outline='')
            canvas.create_text(lx + 12, legend_y + 5, text=label,
                               anchor='w', font=('Arial', 7), fill='#333')
            lx += 90

    @staticmethod
    def _draw_range_comparison_chart(canvas):
        """在 Canvas 上绘制均值与范围对比图：每人一行，展示 min-mean-max 范围条，整体均值和规格线"""
        person_table = getattr(canvas, '_person_table', None)
        full_info = getattr(canvas, '_full_info', None)
        if not person_table:
            return

        canvas.delete('all')
        w = canvas.winfo_width()
        h = canvas.winfo_height()
        if w < 100 or h < 80:
            return

        # 提取数据
        names = []
        mins = []
        maxes = []
        means = []
        highlight = []
        for row in person_table:
            names.append(str(row.get('检验人', '')))
            mins.append(float(row.get('最小值', 0)))
            maxes.append(float(row.get('最大值', 0)))
            means.append(float(row.get('均值', 0)))
            highlight.append('← 异常' in str(row.get('备注', '')))

        n_people = len(names)
        if n_people == 0:
            return

        # 计算整体均值
        overall_mean = sum(means) / len(means) if means else 0

        # 尝试从 full_info 获取规格限
        spec_min = None
        spec_max = None
        if full_info:
            # 规格限可能在多个字段中
            for key in ('整体正常下限', '整体规格内正常下限', '判断最小值'):
                if key in full_info:
                    try:
                        spec_min = float(full_info[key])
                        break
                    except (ValueError, TypeError):
                        pass
            for key in ('整体正常上限', '整体规格内正常上限', '判断最大值'):
                if key in full_info:
                    try:
                        spec_max = float(full_info[key])
                        break
                    except (ValueError, TypeError):
                        pass

        # 确定图表数值范围
        all_vals = mins + maxes + means + [overall_mean]
        if spec_min is not None:
            all_vals.append(spec_min)
        if spec_max is not None:
            all_vals.append(spec_max)
        val_min = min(all_vals)
        val_max = max(all_vals)
        val_range = val_max - val_min
        if val_range < 0.001:
            val_range = 1.0

        # 边距
        left_m = 65
        right_m = 40
        top_m = 15
        bottom_m = 20
        plot_w = w - left_m - right_m
        plot_h = h - top_m - bottom_m

        # 每人行高
        row_h = min(35, max(15, plot_h / n_people))
        total_rows_h = row_h * n_people

        def val_to_x(v):
            return left_m + (v - val_min) / val_range * plot_w

        # 网格线
        n_grid = 5
        for i in range(n_grid + 1):
            frac = i / n_grid
            x = left_m + frac * plot_w
            v = val_min + frac * val_range
            canvas.create_line(x, top_m, x, top_m + total_rows_h, fill='#f0f0f0')
            canvas.create_text(x, top_m + total_rows_h + 8,
                               text=f'{v:.2f}', font=('Arial', 6), fill='#666')

        # 为每人画范围条和均值点
        for i in range(n_people):
            y_center = top_m + i * row_h + row_h / 2
            y_top = y_center - row_h * 0.3
            y_bottom = y_center + row_h * 0.3

            # 范围条（min 到 max）
            x1 = val_to_x(mins[i])
            x2 = val_to_x(maxes[i])
            bar_color = '#E74C3C' if highlight[i] else '#5B9BD5'
            canvas.create_rectangle(x1, y_top, x2, y_bottom,
                                    fill=bar_color, outline='', stipple='')

            # 范围条边框
            canvas.create_rectangle(x1, y_top, x2, y_bottom,
                                    fill='', outline=bar_color, width=1)

            # 均值点（菱形）
            mx = val_to_x(means[i])
            d = max(2, min(6, row_h * 0.25))
            canvas.create_polygon(
                mx, y_center - d, mx + d, y_center,
                mx, y_center + d, mx - d, y_center,
                fill='white', outline=bar_color, width=2
            )

            # 标签
            label = names[i]
            if highlight[i]:
                label += ' ←'
            text_color = '#C0392B' if highlight[i] else '#333'
            canvas.create_text(left_m - 5, y_center,
                               text=label, anchor='e', font=('微软雅黑', 8),
                               fill=text_color)

            # 右侧数值标注
            canvas.create_text(val_to_x(maxes[i]) + 24, y_center,
                               text=f'{mins[i]:.2f}~{maxes[i]:.2f}',
                               anchor='w', font=('Arial', 6), fill='#888')

        # 整体均值竖线
        om_x = val_to_x(overall_mean)
        canvas.create_line(om_x, top_m, om_x, top_m + total_rows_h,
                           fill='#2C3E50', width=2, dash=(8, 3))
        canvas.create_text(om_x, top_m - 7,
                           text=f'整体均值={overall_mean:.2f}',
                           font=('Arial', 7, 'bold'), fill='#2C3E50')

        # 规格限竖线（如果有）
        if spec_min is not None:
            smin_x = val_to_x(spec_min)
            canvas.create_line(smin_x, top_m, smin_x, top_m + total_rows_h,
                               fill='#E67E22', width=1.5, dash=(4, 3))
            canvas.create_text(smin_x, top_m - 7,
                               text=f'下限={spec_min:.2f}',
                               font=('Arial', 6), fill='#E67E22')

        if spec_max is not None:
            smax_x = val_to_x(spec_max)
            canvas.create_line(smax_x, top_m, smax_x, top_m + total_rows_h,
                               fill='#E67E22', width=1.5, dash=(4, 3))
            canvas.create_text(smax_x, top_m - 7,
                               text=f'上限={spec_max:.2f}',
                               font=('Arial', 6), fill='#E67E22')

    # ==================== 异常5：测试数据规律性分布 ====================

    def _check_pattern_distribution(self, cols):
        """
        异常5：相同测试项目数据呈规律性分布（人为编造的迹象）。
        """
        results = []
        task_col = cols['task']
        item_col = cols['item']
        content_col = cols['content']
        person_col = cols['person']

        groups = self.df.groupby([item_col, content_col, task_col])

        for (item, content, task), group in groups:
            vals = group['_num_value'].tolist()
            clean_vals = [
                v for v in vals
                if isinstance(v, (int, float)) and not (isinstance(v, float) and math.isnan(v))
            ]

            if len(clean_vals) < 6:
                continue

            patterns = []
            n = len(clean_vals)

            # 检测1：连续相同值比例
            same_count = 0
            for i in range(1, n):
                if abs(clean_vals[i] - clean_vals[i - 1]) < 1e-9:
                    same_count += 1
            if same_count > n * 0.4:
                patterns.append(f'连续相同值比例 {same_count / n:.0%} ({same_count + 1}/{n})')

            # 检测2：严格单调
            increasing = all(clean_vals[i] > clean_vals[i - 1] for i in range(1, n))
            decreasing = all(clean_vals[i] < clean_vals[i - 1] for i in range(1, n))
            if increasing:
                patterns.append('严格递增序列')
            elif decreasing:
                patterns.append('严格递减序列')

            # 检测3：周期重复
            if n >= 8:
                half = n // 2
                first_half = clean_vals[:half]
                second_half = clean_vals[half:half * 2]
                if first_half == second_half:
                    patterns.append(f'周期重复（前半=后半, 周期={half}）')

            # 检测4：变异系数极小
            try:
                mean_val = statistics.mean(clean_vals)
                std_val = statistics.stdev(clean_vals)
                if mean_val != 0:
                    cv = std_val / abs(mean_val)
                    if cv < 0.01 and n >= 8:
                        patterns.append(f'数值极度集中 (CV={cv:.4f})')
            except (statistics.StatisticsError, ZeroDivisionError):
                pass

            if patterns:
                persons = group[person_col].dropna().unique()
                results.append({
                    '异常类型': '数据异常-测试数据规律性分布',
                    '检验项目/SN': str(item),
                    '检验人/站点': f'检验人: {", ".join(persons.astype(str))}',
                    '任务单/统计信息': f'任务单: {str(task)}, {n}个值',
                    '详情': '; '.join(patterns),
                    '备注': f'检验内容: {str(content)[:60]}',
                    '_full_info': {
                        '检验项目': str(item),
                        '检验内容': str(content),
                        '任务单': str(task),
                        '检验人': persons.tolist(),
                        '数据点数': n,
                        '规律类型': patterns,
                        '前50个值': ','.join(str(v) for v in clean_vals[:50]),
                    }
                })

        return results

    # ==================== 异常6：人员连续出现 ====================

    def _check_person_consecutive(self, cols):
        """
        异常6：检验人或测量值修改人连续N天出现（全局检测，N可配置，默认7）。

        时间口径：
        - 检验人按「扫入时间」判定
        - 测量值修改人按「测量值修改时间」判定
        - 一天按 8:00~次日8:00 划分（白班 8:00~20:00 与夜班 20:00~次日8:00 视为同一天），
          而非 0:00~0:00 自然日。
        """
        results = []
        scan_time_col = self.col_scan_time.get().strip()
        modify_time_col = self.col_modify_time.get().strip()
        modifier_col = self.col_modifier.get().strip()
        n_days = self.consecutive_days_var.get()

        person_col = cols['person']
        has_scan_time = bool(scan_time_col and scan_time_col in self.df.columns)
        has_modifier = bool(modifier_col and modifier_col in self.df.columns)
        has_modify_time = bool(modify_time_col and modify_time_col in self.df.columns)

        if not has_scan_time and not (has_modifier and has_modify_time):
            self._log('注意: 扫入时间/测量值修改时间列均不存在，跳过异常6（人员连续出现）')
            return results

        # 各角色使用各自的时间列解析
        def _parse_time(col):
            try:
                return pd.to_datetime(self.df[col], errors='coerce')
            except Exception:
                return None

        scan_times = _parse_time(scan_time_col) if has_scan_time else None
        modify_times = _parse_time(modify_time_col) if (has_modifier and has_modify_time) else None

        # 预计算：各人员作为检验人/修改人的出现日期（班次日，8:00为界），
        # 用 groupby 一次性聚合，避免逐人全表布尔掩码（O(N*P) -> O(N)）
        def _days_by_person(person_col_name, time_series):
            if time_series is None:
                return {}
            p = self.df[person_col_name]
            valid = p.notna() & time_series.notna()
            if not valid.any():
                return {}
            days = (time_series - pd.Timedelta(hours=8)).dt.date
            tmp = pd.DataFrame({'p': p[valid].values, 'd': days[valid].values})
            out = {}
            for person, g in tmp.groupby('p')['d']:
                out[person] = sorted(set(g.tolist()))
            return out

        inspector_days_map = _days_by_person(person_col, scan_times)
        modifier_days_map = _days_by_person(modifier_col, modify_times) if (has_modifier and has_modify_time) else {}

        # 全局收集所有人员及其身份（用于判定"检验人/修改人"）
        inspector_persons = set(self.df[person_col].dropna().unique())
        modifier_persons = set(self.df[modifier_col].dropna().unique()) if has_modifier else set()
        persons_to_check = inspector_persons | modifier_persons

        for person in persons_to_check:
            person_str = str(person)
            if not person_str or person_str in ('nan', 'None', ''):
                continue

            person_days = []
            if has_scan_time:
                person_days.extend(inspector_days_map.get(person, []))
            if has_modifier and has_modify_time:
                person_days.extend(modifier_days_map.get(person, []))

            if len(person_days) < n_days:
                continue

            unique_days = sorted(set(person_days))

            # 检查是否存在连续N天的窗口
            has_consecutive = False
            consecutive_start = None
            consecutive_end = None
            for i in range(len(unique_days) - n_days + 1):
                start = unique_days[i]
                end = unique_days[i + n_days - 1]
                if (end - start).days == n_days - 1:
                    has_consecutive = True
                    consecutive_start = start
                    consecutive_end = end
                    break

            if not has_consecutive:
                continue

            # 判断人员类型
            person_type = '检验人'
            if has_modifier:
                is_inspector = person in inspector_persons
                is_modifier_p = person in modifier_persons
                if is_inspector and is_modifier_p:
                    person_type = '检验人+修改人'
                elif is_modifier_p:
                    person_type = '修改人'

            # 收集涉及的项目和内容（仅在判定为异常时计算）
            inspector_mask = self.df[person_col] == person
            modifier_mask = self.df[modifier_col] == person if has_modifier else pd.Series(False, index=self.df.index)
            person_rows = self.df[inspector_mask | modifier_mask]
            involved_items = person_rows[cols['item']].dropna().unique()
            involved_contents = person_rows[cols['content']].dropna().unique()

            results.append({
                '异常类型': '数据异常-人员连续出现',
                '检验项目/SN': ', '.join(str(x) for x in involved_items[:5]),
                '检验人/站点': f'{person_type}: {person_str}',
                '任务单/统计信息': f'连续出现 {len(unique_days)} 天',
                '详情': f'连续{n_days}天: {consecutive_start} ~ {consecutive_end}',
                '备注': f'涉及{len(involved_items)}个项目',
                '_full_info': {
                    '人员': person_str,
                    '人员类型': person_type,
                    '涉及项目': [str(x) for x in involved_items],
                    '涉及检验内容': [str(x) for x in involved_contents],
                    '出现日期': [str(d) for d in unique_days],
                    '连续区间': f'{consecutive_start} ~ {consecutive_end}',
                    '连续天数阈值': n_days,
                    '出现天数': len(unique_days),
                }
            })

        return results

    # ==================== 异常7：计量型测试值为空 ====================

    def _check_empty_measurement_value(self, cols, spec_min_col=None, spec_max_col=None,
                                       result_col=None):
        """
        异常7：计量型测试值为空（且结果为OK）。

        判定规则：
        - 计量型判定：判断最小值 或 判断最大值 至少一个为数值型且不为空 → 该行为计量型
        - 空值判定：测量值为空（NaN、空字符串、纯空格）
          注意：填写 NA / na / N/A / Na 等不算空
        - 结果判定：结果列为 OK（仅当结果列存在时启用该条件）
        - 计量型 且 测量值为空 且 结果为OK → 判为异常（逐行记录）
        """
        results = []

        has_min = spec_min_col is not None and spec_min_col in self.df.columns
        has_max = spec_max_col is not None and spec_max_col in self.df.columns
        if not has_min and not has_max:
            self._log('注意: 判断最小值/最大值列均不存在，跳过异常7（计量型测试值为空）')
            return results

        has_result = result_col is not None and result_col in self.df.columns
        if not has_result:
            self._log(f'注意: 结果列"{result_col}"不存在，无法判断结果是否为OK，跳过异常7')
            return results

        value_col = cols['value']

        # 计量型判定：两个规格列任一可转为数值即为计量型
        if has_min:
            spec_min_num = _to_numeric_series(self.df[spec_min_col])
        else:
            spec_min_num = pd.Series(np.nan, index=self.df.index)
        if has_max:
            spec_max_num = _to_numeric_series(self.df[spec_max_col])
        else:
            spec_max_num = pd.Series(np.nan, index=self.df.index)

        quantitative_mask = spec_min_num.notna() | spec_max_num.notna()

        # 空值判定：NaN / 空串 / 纯空格；NA/na/N/A/Na 等字符串不算空
        raw_vals = self.df[value_col]
        empty_mask = raw_vals.isna() | (raw_vals.astype(str).str.strip() == '')

        # 结果判定：结果为 OK（去首尾空格后精确匹配）
        ok_mask = self.df[result_col].astype(str).str.strip() == 'OK'

        anomaly_df = self.df[quantitative_mask & empty_mask & ok_mask]
        if anomaly_df.empty:
            return results

        item_col = cols['item']
        content_col = cols['content']
        person_col = cols['person']
        sn_col = cols['sn']
        station_col = cols['station']
        task_col = cols['task']

        def _s(v):
            return '' if pd.isna(v) else str(v).strip()

        for idx, row in anomaly_df.iterrows():
            spec_min_str = _s(row[spec_min_col]) if has_min else ''
            spec_max_str = _s(row[spec_max_col]) if has_max else ''

            results.append({
                '异常类型': '数据异常-计量型测试值为空',
                '检验项目/SN': f'{_s(row[item_col])} / SN: {_s(row[sn_col])}',
                '检验人/站点': f'检验人: {_s(row[person_col])} / 站点: {_s(row[station_col])}',
                '任务单/统计信息': f'任务单: {_s(row[task_col])}',
                '详情': (
                    f'计量型检测项（判断最小值: {spec_min_str or "空"}, '
                    f'判断最大值: {spec_max_str or "空"}），测量值为空，结果为OK'
                ),
                '备注': f'检验内容: {_s(row[content_col])[:60]}',
                '_full_info': {
                    '检验项目': _s(row[item_col]),
                    '检验内容': _s(row[content_col]),
                    'SN': _s(row[sn_col]),
                    '检验人': _s(row[person_col]),
                    '适用站点': _s(row[station_col]),
                    '任务单号': _s(row[task_col]),
                    '判断最小值': spec_min_str,
                    '判断最大值': spec_max_str,
                    '测量值': '',
                    '结果': _s(row[result_col]),
                    '行号': int(idx) + 2,  # Excel行号（含表头）
                }
            })

        return results

    # ==================== 结果显示 ====================

    def _get_filtered_anomalies(self):
        filtered = []
        for a in self.anomalies:
            atype = a['异常类型']
            if atype in self.show_types and not self.show_types[atype].get():
                continue
            filtered.append(a)
        return filtered

    def _refresh_tree(self):
        for item in self.tree.get_children():
            self.tree.delete(item)

        filtered = self._get_filtered_anomalies()

        for i, a in enumerate(filtered, 1):
            self.tree.insert('', tk.END, values=(
                i,
                a['异常类型'],
                a['检验项目/SN'],
                a['检验人/站点'],
                a['任务单/统计信息'],
                a['详情'],
                a['备注'],
            ))

    def _on_double_click(self, event):
        selection = self.tree.selection()
        if not selection:
            return
        item = selection[0]
        values = self.tree.item(item, 'values')
        if not values:
            return

        idx = int(values[0]) - 1
        filtered = self._get_filtered_anomalies()
        if idx >= len(filtered):
            return

        a = filtered[idx]
        full_info = a.get('_full_info', {})
        full_values = a.get('_full_values', '')

        is_anomaly4 = a['异常类型'] == '数据异常-不同人员数据分布不一致'
        person_table = full_info.get('_person_stats_table')
        dist_chart = full_info.get('_distribution_chart')

        # 根据内容确定窗口大小和布局
        has_tables = is_anomaly4 and (person_table or dist_chart)
        if has_tables:
            if dist_chart:
                detail_win = tk.Toplevel(self.root)
                detail_win.title(f'详细信息 - 第{idx + 1}条')
                detail_win.geometry('900x650+400+100')
            else:
                detail_win = tk.Toplevel(self.root)
                detail_win.title(f'详细信息 - 第{idx + 1}条')
                detail_win.geometry('820x520+500+200')
        else:
            detail_win = tk.Toplevel(self.root)
            detail_win.title(f'详细信息 - 第{idx + 1}条')
            detail_win.geometry('750x400+500+200')

        if not has_tables:
            detail_win.columnconfigure(0, weight=1)
            detail_win.rowconfigure(0, weight=1)
            text = scrolledtext.ScrolledText(detail_win, font=('宋体', 11), wrap=tk.WORD)
            text.grid(row=0, column=0, sticky='nsew', padx=10, pady=10)
        else:
            # 有表格时：使用 Notebook 分区展示
            nb = ttk.Notebook(detail_win)
            nb.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

            # --- Tab 1：人员统计表 ---
            if person_table:
                stat_frame = ttk.Frame(nb)
                nb.add(stat_frame, text='人员统计')
                stat_frame.columnconfigure(0, weight=1)
                stat_frame.rowconfigure(0, weight=1)
                stat_frame.rowconfigure(1, weight=2)

                pt_cols = list(person_table[0].keys())
                pt_tree = ttk.Treeview(stat_frame, columns=pt_cols,
                                       show='headings', height=min(len(person_table) + 1, 6))
                pt_tree.grid(row=0, column=0, sticky='nsew', padx=3, pady=(3, 0))

                pt_vsb = ttk.Scrollbar(stat_frame, orient='vertical', command=pt_tree.yview)
                pt_vsb.grid(row=0, column=1, sticky='ns')
                pt_tree.configure(yscrollcommand=pt_vsb.set)

                for col in pt_cols:
                    pt_tree.heading(col, text=col)
                    pt_tree.column(col, width=85, anchor='center')

                for row_data in person_table:
                    vals = [row_data.get(c, '') for c in pt_cols]
                    iid = pt_tree.insert('', tk.END, values=vals)
                    if '← 异常' in str(row_data.get('备注', '')):
                        pt_tree.item(iid, tags=('anomaly',))
                pt_tree.tag_configure('anomaly', background='#FFD4D4')

                # 均值与范围对比图
                range_canvas = tk.Canvas(stat_frame, bg='white', highlightthickness=1,
                                          highlightbackground='#ccc')
                range_canvas.grid(row=1, column=0, sticky='nsew', padx=3, pady=(5, 3))
                range_canvas._person_table = person_table
                range_canvas._full_info = full_info
                range_canvas.bind('<Configure>',
                                   lambda e: self._draw_range_comparison_chart(e.widget))

            # --- Tab 2：热点分布对比 ---
            if dist_chart:
                dist_frame = ttk.Frame(nb)
                nb.add(dist_frame, text='分布对比')
                dist_frame.columnconfigure(0, weight=1)
                dist_frame.rowconfigure(0, weight=1)
                dist_frame.rowconfigure(1, weight=2)

                # 表格
                dc_cols = list(dist_chart[0].keys())
                dc_tree = ttk.Treeview(dist_frame, columns=dc_cols,
                                       show='headings', height=min(len(dist_chart) + 1, 8))
                dc_tree.grid(row=0, column=0, sticky='nsew', padx=3, pady=(3, 0))

                dc_vsb = ttk.Scrollbar(dist_frame, orient='vertical', command=dc_tree.yview)
                dc_vsb.grid(row=0, column=1, sticky='ns')
                dc_tree.configure(yscrollcommand=dc_vsb.set)

                for col in dc_cols:
                    dc_tree.heading(col, text=col)
                    col_width = 90 if '←' not in col else 100
                    dc_tree.column(col, width=col_width, anchor='center')

                for row_data in dist_chart:
                    vals = [row_data.get(c, '') for c in dc_cols]
                    iid = dc_tree.insert('', tk.END, values=vals)
                    for ci, col in enumerate(dc_cols):
                        if '←' in col:
                            dc_tree.set(iid, ci, str(row_data.get(col, '')))

                # 柱状图
                chart_canvas = tk.Canvas(dist_frame, bg='white', highlightthickness=1,
                                          highlightbackground='#ccc')
                chart_canvas.grid(row=1, column=0, sticky='nsew', padx=3, pady=(5, 3))
                # 延迟绑定 resize 重绘
                chart_canvas._dist_chart_data = dist_chart
                chart_canvas.bind('<Configure>',
                                   lambda e: self._draw_distribution_chart(e.widget))

            # --- Tab 3：文本详情 ---
            detail_frame = ttk.Frame(nb)
            nb.add(detail_frame, text='详情')
            detail_frame.columnconfigure(0, weight=1)
            detail_frame.rowconfigure(0, weight=1)
            text = scrolledtext.ScrolledText(detail_frame, font=('宋体', 11), wrap=tk.WORD)
            text.grid(row=0, column=0, sticky='nsew', padx=5, pady=5)

        info = f"异常类型: {a['异常类型']}\n"
        info += f"{'=' * 60}\n"
        for key, val in full_info.items():
            if key.startswith('_'):
                continue
            if isinstance(val, dict):
                info += f"\n{key}:\n"
                for k, v in val.items():
                    info += f"  {k}: {v}\n"
            elif isinstance(val, list):
                if len(val) > 0 and isinstance(val[0], dict):
                    continue  # 表格数据已在上面显示
                val_str = ', '.join(str(x) for x in val)
                if len(val_str) > 120:
                    val_str = val_str[:117] + '...'
                info += f"{key}: [{val_str}]\n"
            else:
                info += f"{key}: {val}\n"

        if full_values:
            parts_count = len(full_values.split(','))
            info += f"\n完整测量值（{parts_count}个）:\n{full_values[:2000]}"

        text.insert(tk.END, info)
        text.config(state=tk.DISABLED)

    # ==================== 检验项目分析 ====================

    def _refresh_inspection_list(self):
        """刷新检验项目列表"""
        self.inspect_listbox.delete(0, tk.END)
        for item in self.inspection_items:
            self.inspect_listbox.insert(tk.END, item)
        if self.inspection_items:
            self.inspect_status.set(f'共 {len(self.inspection_items)} 条检验项目，双击查看详情')

    def _get_selected_inspection_item(self):
        """获取当前选中的检验项目"""
        selection = self.inspect_listbox.curselection()
        if not selection:
            return None
        return self.inspection_items[selection[0]]

    def _on_inspection_double_click(self, event):
        """双击检验项目列表项"""
        self._open_inspection_detail()

    def _on_inspection_detail_click(self):
        """点击查看详情按钮"""
        self._open_inspection_detail()

    def _open_inspection_detail(self):
        """打开检验项目详情窗口"""
        item_name = self._get_selected_inspection_item()
        if not item_name:
            messagebox.showwarning('提示', '请先选择一条检验项目')
            return
        if self.df is None:
            messagebox.showwarning('提示', '请先加载数据文件并完成分析')
            return

        # 从数据中筛选该检验项目的数据
        content_col = self.col_content.get().strip()
        item_col = self.col_item.get().strip()
        person_col = self.col_person.get().strip()
        value_col = self.col_value.get().strip()
        task_col = self.col_task.get().strip()
        sn_col = self.col_sn.get().strip()

        # 匹配检验项目（支持部分匹配）
        mask = (
            self.df[content_col].astype(str).str.contains(item_name, na=False, regex=False) |
            self.df[item_col].astype(str).str.contains(item_name, na=False, regex=False)
        )
        filtered_df = self.df[mask].copy()

        if filtered_df.empty:
            messagebox.showwarning('提示', f'未找到与"{item_name}"匹配的数据')
            return

        # 创建详情窗口
        detail_win = tk.Toplevel(self.root)
        detail_win.title(f'检验项目详情 - {item_name}')
        detail_win.geometry('1000x700+300+60')

        # 顶部工具栏
        toolbar = ttk.Frame(detail_win)
        toolbar.pack(side=tk.TOP, fill=tk.X, padx=5, pady=(5, 0))

        ttk.Label(toolbar, text=f'检验项目: {item_name}',
                  font=('微软雅黑', 11, 'bold')).pack(side=tk.LEFT, padx=5)

        # Notebook with tabs
        nb = ttk.Notebook(detail_win)
        nb.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        # ---- Tab 1: 数据汇总 ----
        summary_frame = ttk.Frame(nb)
        nb.add(summary_frame, text='数据汇总')
        summary_frame.columnconfigure(0, weight=1)
        summary_frame.rowconfigure(0, weight=1)
        summary_frame.rowconfigure(1, weight=0)
        summary_frame.rowconfigure(2, weight=2)

        # 收集规格限
        spec_min = None
        spec_max = None
        smin_col = self.col_spec_min.get().strip()
        smax_col = self.col_spec_max.get().strip()
        if smin_col and smax_col and smin_col in filtered_df.columns and smax_col in filtered_df.columns:
            spec_min_vals = filtered_df[smin_col].dropna()
            spec_max_vals = filtered_df[smax_col].dropna()
            if len(spec_min_vals) > 0:
                spec_min = float(spec_min_vals.median())
            if len(spec_max_vals) > 0:
                spec_max = float(spec_max_vals.median())

        # 按检验人分组统计
        person_groups = filtered_df.groupby(person_col)
        stats_data = []
        person_values_map = {}  # {检验人: [values]}
        for person, group in person_groups:
            vals = group['_num_value'].dropna().tolist()
            if not vals:
                continue
            person_values_map[str(person)] = vals
            stats_data.append({
                '检验人': str(person),
                '数目': len(vals),
                '最大值': round(max(vals), 4),
                '最小值': round(min(vals), 4),
                '均值': round(statistics.mean(vals), 4),
                '标准差': round(statistics.stdev(vals), 4) if len(vals) > 1 else 0,
                '中位数': round(statistics.median(vals), 4),
            })

        if stats_data:
            stats_cols = ['检验人', '数目', '最大值', '最小值', '均值', '标准差', '中位数']
            stats_tree = ttk.Treeview(summary_frame, columns=stats_cols,
                                      show='headings', height=min(len(stats_data) + 1, 8))
            stats_tree.grid(row=0, column=0, sticky='nsew', padx=3, pady=(3, 0))

            vsb = ttk.Scrollbar(summary_frame, orient='vertical', command=stats_tree.yview)
            vsb.grid(row=0, column=1, sticky='ns')
            stats_tree.configure(yscrollcommand=vsb.set)

            for col in stats_cols:
                stats_tree.heading(col, text=col)
                stats_tree.column(col, width=100, anchor='center')

            for row_data in stats_data:
                vals_row = [row_data.get(c, '') for c in stats_cols]
                stats_tree.insert('', tk.END, values=vals_row)

            # 汇总信息
            all_vals = filtered_df['_num_value'].dropna().tolist()
            info_text = (
                f"总数据量: {len(all_vals)} | "
                f"检验人数: {len(stats_data)} | "
                f"整体均值: {statistics.mean(all_vals):.4f} | "
                f"整体最大值: {max(all_vals):.4f} | "
                f"整体最小值: {min(all_vals):.4f} | "
                f"整体标准差: {statistics.stdev(all_vals):.4f}" if len(all_vals) > 1
                else f"总数据量: {len(all_vals)}"
            )
            ttk.Label(summary_frame, text=info_text,
                      font=('微软雅黑', 9), foreground='#555').grid(
                row=1, column=0, sticky='w', padx=3, pady=(0, 3))

            # 箱线图+散点图
            box_canvas = tk.Canvas(summary_frame, bg='white', highlightthickness=1,
                                    highlightbackground='#ccc')
            box_canvas.grid(row=2, column=0, sticky='nsew', padx=3, pady=3)
            box_canvas._person_values = person_values_map
            box_canvas._item_name = item_name
            box_canvas._spec_min = spec_min
            box_canvas._spec_max = spec_max
            box_canvas._stats_data = stats_data
            box_canvas.bind('<Configure>',
                            lambda e: self._draw_box_scatter_chart(e.widget))

        # ---- Tab 2: 异常分析 ----
        anomaly_frame = ttk.Frame(nb)
        nb.add(anomaly_frame, text='异常分析')
        anomaly_frame.columnconfigure(0, weight=1)
        anomaly_frame.rowconfigure(0, weight=1)

        # 筛选与该检验项目相关的异常
        related_anomalies = []
        for a in self.anomalies:
            detail1 = a.get('检验项目/SN', '')
            full_info = a.get('_full_info', {})
            check_item = full_info.get('检验项目', '')
            check_content = full_info.get('检验内容', '')
            if item_name in detail1 or item_name in str(check_item) or item_name in str(check_content):
                related_anomalies.append(a)

        if related_anomalies:
            a_cols = ['异常类型', '检验项目/SN', '检验人/站点', '任务单/统计信息', '详情', '备注']
            a_tree = ttk.Treeview(anomaly_frame, columns=a_cols,
                                  show='headings', height=min(len(related_anomalies) + 1, 15))
            a_tree.grid(row=0, column=0, sticky='nsew', padx=3, pady=3)

            avsb = ttk.Scrollbar(anomaly_frame, orient='vertical', command=a_tree.yview)
            avsb.grid(row=0, column=1, sticky='ns')
            a_tree.configure(yscrollcommand=avsb.set)

            a_tree.heading('异常类型', text='异常类型')
            a_tree.column('异常类型', width=230, anchor='w')
            a_tree.heading('检验项目/SN', text='检验项目/SN')
            a_tree.column('检验项目/SN', width=200, anchor='w')
            a_tree.heading('检验人/站点', text='检验人/站点')
            a_tree.column('检验人/站点', width=160, anchor='w')
            a_tree.heading('任务单/统计信息', text='任务单/统计信息')
            a_tree.column('任务单/统计信息', width=160, anchor='w')
            a_tree.heading('详情', text='详情')
            a_tree.column('详情', width=250, anchor='w')
            a_tree.heading('备注', text='备注')
            a_tree.column('备注', width=160, anchor='w')

            for a in related_anomalies:
                a_tree.insert('', tk.END, values=(
                    a['异常类型'], a['检验项目/SN'], a['检验人/站点'],
                    a['任务单/统计信息'], a['详情'], a['备注'],
                ))
        else:
            ttk.Label(anomaly_frame, text='未发现与此检验项目相关的异常记录',
                      font=('微软雅黑', 11), foreground='green').grid(
                row=0, column=0, padx=20, pady=40)

        # ---- Tab 3: 正态分布 ----
        dist_frame = ttk.Frame(nb)
        nb.add(dist_frame, text='正态分布')
        dist_frame.columnconfigure(0, weight=1)
        dist_frame.rowconfigure(0, weight=1)

        dist_canvas = tk.Canvas(dist_frame, bg='white', highlightthickness=1,
                                highlightbackground='#ccc')
        dist_canvas.grid(row=0, column=0, sticky='nsew', padx=5, pady=5)
        dist_canvas._data = filtered_df['_num_value'].dropna().tolist()
        dist_canvas._item_name = item_name
        dist_canvas.bind('<Configure>', lambda e: self._draw_normal_distribution(e.widget))

        # ---- Tab 4: CPK分析 ----
        cpk_frame = ttk.Frame(nb)
        nb.add(cpk_frame, text='CPK分析')
        cpk_frame.columnconfigure(0, weight=1)
        cpk_frame.rowconfigure(0, weight=1)

        cpk_text = scrolledtext.ScrolledText(cpk_frame, font=('宋体', 11), wrap=tk.WORD)
        cpk_text.grid(row=0, column=0, sticky='nsew', padx=5, pady=5)

        # 计算CPK
        vals_cpk = filtered_df['_num_value'].dropna().tolist()
        if len(vals_cpk) >= 5:
            mean_val = statistics.mean(vals_cpk)
            std_val = statistics.stdev(vals_cpk) if len(vals_cpk) > 1 else 0

            # 尝试从数据中获取规格限
            spec_min = None
            spec_max = None
            smin_col = self.col_spec_min.get().strip()
            smax_col = self.col_spec_max.get().strip()
            if smin_col and smax_col and smin_col in filtered_df.columns and smax_col in filtered_df.columns:
                spec_min_vals = filtered_df[smin_col].dropna()
                spec_max_vals = filtered_df[smax_col].dropna()
                if len(spec_min_vals) > 0:
                    spec_min = spec_min_vals.median()
                if len(spec_max_vals) > 0:
                    spec_max = spec_max_vals.median()

            cpk_info = f"CPK 分析 - {item_name}\n"
            cpk_info += f"{'=' * 60}\n"
            cpk_info += f"数据点数: {len(vals_cpk)}\n"
            cpk_info += f"均值 (μ): {mean_val:.6f}\n"
            cpk_info += f"标准差 (σ): {std_val:.6f}\n"

            if spec_min is not None and spec_max is not None and std_val > 0:
                cpk_lower = (mean_val - spec_min) / (3 * std_val)
                cpk_upper = (spec_max - mean_val) / (3 * std_val)
                cpk = min(cpk_lower, cpk_upper)
                cp_status = '优秀' if cpk >= 1.67 else '良好' if cpk >= 1.33 else '一般' if cpk >= 1.0 else '不足'
                cpk_info += f"\n规格下限 (LSL): {spec_min:.6f}\n"
                cpk_info += f"规格上限 (USL): {spec_max:.6f}\n"
                cpk_info += f"Cpk (下限): {cpk_lower:.4f}\n"
                cpk_info += f"Cpk (上限): {cpk_upper:.4f}\n"
                cpk_info += f"Cpk = {cpk:.4f} (等级: {cp_status})\n"
            else:
                cpk_info += (
                    "\n(未设置规格限或无标准差数据，无法计算CPK。"
                    "\n请在列名映射中设置'判断最小值'和'判断最大值'列。)"
                )
        else:
            cpk_info = f"数据点不足（当前{len(vals_cpk)}个），需要至少5个数据点"

        cpk_text.insert(tk.END, cpk_info)
        cpk_text.config(state=tk.DISABLED)

        # ---- Tab 5: 控制图 ----
        control_frame = ttk.Frame(nb)
        nb.add(control_frame, text='控制图')
        control_frame.columnconfigure(0, weight=1)
        control_frame.rowconfigure(0, weight=1)

        ctrl_canvas = tk.Canvas(control_frame, bg='white', highlightthickness=1,
                                highlightbackground='#ccc')
        ctrl_canvas.grid(row=0, column=0, sticky='nsew', padx=5, pady=5)
        ctrl_canvas._data = filtered_df['_num_value'].dropna().tolist()
        ctrl_canvas._item_name = item_name
        ctrl_canvas.bind('<Configure>', lambda e: self._draw_control_chart(e.widget))

        # ---- Tab 6: 按钮集合 ----
        btn_frame = ttk.Frame(nb)
        nb.add(btn_frame, text='按钮集合')
        btn_frame.columnconfigure(0, weight=1)
        btn_frame.rowconfigure(0, weight=1)

        center_btn_frame = ttk.Frame(btn_frame)
        center_btn_frame.place(relx=0.5, rely=0.5, anchor='center')

        def _export_data():
            path = filedialog.asksaveasfilename(
                title='导出数据',
                defaultextension='.xlsx',
                filetypes=[('Excel 文件', '*.xlsx'), ('所有文件', '*.*')],
                initialfile=f'{item_name}_数据汇总_{datetime.now().strftime("%Y%m%d_%H%M%S")}.xlsx'
            )
            if path:
                try:
                    # 导出汇总统计
                    if stats_data:
                        pd.DataFrame(stats_data).to_excel(
                            path, sheet_name='数据汇总', index=False)
                    # 导出原始数据
                    with pd.ExcelWriter(path, engine='openpyxl', mode='a' if stats_data else 'w') as writer:
                        filtered_df.to_excel(writer, sheet_name='原始数据', index=False)
                    self._log(f'数据已导出到: {path}')
                    messagebox.showinfo('成功', f'数据已导出到:\n{path}')
                except Exception as e:
                    messagebox.showerror('错误', f'导出失败: {e}')

        def _export_chart():
            path = filedialog.asksaveasfilename(
                title='导出图表',
                defaultextension='.png',
                filetypes=[('PNG 图片', '*.png'), ('所有文件', '*.*')],
                initialfile=f'{item_name}_控制图_{datetime.now().strftime("%Y%m%d_%H%M%S")}.png'
            )
            if path:
                self._log(f'图表导出功能：{path}（需安装PIL库支持PNG导出）')
                messagebox.showinfo('提示',
                    '图表导出需要PIL(Pillow)库支持。\n'
                    '图表数据已包含在Excel导出中。')

        def _copy_stats():
            if not stats_data:
                return
            text = '\t'.join(stats_cols) + '\n'
            for row in stats_data:
                text += '\t'.join(str(row.get(c, '')) for c in stats_cols) + '\n'
            self.root.clipboard_clear()
            self.root.clipboard_append(text)
            messagebox.showinfo('成功', '统计数据已复制到剪贴板')

        ttk.Button(center_btn_frame, text='导出数据汇总\n(Excel)',
                   command=_export_data, width=18).pack(pady=8)
        ttk.Button(center_btn_frame, text='导出图表\n(PNG)',
                   command=_export_chart, width=18).pack(pady=8)
        ttk.Button(center_btn_frame, text='复制统计数据',
                   command=_copy_stats, width=18).pack(pady=8)
        ttk.Button(center_btn_frame, text='重新分析',
                   command=lambda: [detail_win.destroy(), self._open_inspection_detail()],
                   width=18).pack(pady=8)

    # ==================== 箱线图+散点图组合 ====================

    @staticmethod
    def _draw_box_scatter_chart(canvas):
        """绘制箱线图+散点图组合，按检验人分组，含规格限线和统计注释"""
        person_values = getattr(canvas, '_person_values', None)
        item_name = getattr(canvas, '_item_name', '')
        spec_min = getattr(canvas, '_spec_min', None)
        spec_max = getattr(canvas, '_spec_max', None)
        stats_data = getattr(canvas, '_stats_data', None)

        if not person_values:
            return

        canvas.delete('all')
        w = canvas.winfo_width()
        h = canvas.winfo_height()
        if w < 100 or h < 80:
            return

        import math as _math
        import random as _random
        _random.seed(42)

        persons = list(person_values.keys())
        n_groups = len(persons)
        if n_groups == 0:
            return

        # 收集所有值用于Y轴范围
        all_vals = []
        for vals in person_values.values():
            all_vals.extend(vals)

        y_min_raw = min(all_vals)
        y_max_raw = max(all_vals)

        # 如果有规格限，扩展范围
        if spec_min is not None:
            y_min_raw = min(y_min_raw, spec_min)
        if spec_max is not None:
            y_max_raw = max(y_max_raw, spec_max)

        y_range = y_max_raw - y_min_raw
        if y_range < 0.001:
            y_range = 1.0
        y_padding = y_range * 0.12
        y_min = y_min_raw - y_padding
        y_max = y_max_raw + y_padding * 2  # 顶部留空间给统计文本

        # 边距（顶部留足空间给标题和统计文本）
        left_m = 75
        right_m = 85
        top_m = 105
        bottom_m = 55
        plot_w = w - left_m - right_m
        plot_h = h - top_m - bottom_m
        if plot_w < 20 or plot_h < 20:
            return

        def val_to_y(v):
            return top_m + plot_h - (v - y_min) / (y_max - y_min) * plot_h

        # 计算每组位置
        group_centers = []
        group_width = plot_w / n_groups
        box_width = group_width * 0.35

        for gi in range(n_groups):
            group_centers.append(left_m + group_width * (gi + 0.5))

        # Y轴网格线和标签
        n_y_ticks = 6
        for i in range(n_y_ticks + 1):
            frac = i / n_y_ticks
            y = top_m + plot_h * (1 - frac)
            val = y_min + frac * (y_max - y_min)
            # 浅灰网格线
            canvas.create_line(left_m, y, left_m + plot_w, y,
                               fill='#CCCCCC', dash=(2, 4))
            canvas.create_text(left_m - 8, y, text=f'{val:.1f}',
                               anchor='e', font=('Arial', 9), fill='#333')

        # 绘制轴线
        canvas.create_line(left_m, top_m + plot_h, left_m + plot_w, top_m + plot_h,
                           fill='#333', width=1.5)  # X轴
        canvas.create_line(left_m, top_m, left_m, top_m + plot_h,
                           fill='#333', width=1.5)  # Y轴

        # 规格限线
        legend_items = []  # [(label, color, dash, linewidth, symbol)]
        if spec_min is not None:
            y_spec = val_to_y(spec_min)
            canvas.create_line(left_m, y_spec, left_m + plot_w, y_spec,
                               fill='#E74C3C', dash=(8, 4), width=1.5)
            canvas.create_text(left_m + plot_w + 3, y_spec,
                               text=f'LSL {spec_min}', anchor='w',
                               font=('Arial', 8, 'bold'), fill='#E74C3C')
            legend_items.append(('LSL', '#E74C3C', True))

        if spec_max is not None:
            y_spec = val_to_y(spec_max)
            canvas.create_line(left_m, y_spec, left_m + plot_w, y_spec,
                               fill='#E74C3C', dash=(8, 4), width=1.5)
            canvas.create_text(left_m + plot_w + 3, y_spec,
                               text=f'USL {spec_max}', anchor='w',
                               font=('Arial', 8, 'bold'), fill='#E74C3C')
            legend_items.append(('USL', '#E74C3C', True))

        # 绘制每组箱线图+散点
        for gi, person in enumerate(persons):
            vals = sorted(person_values[person])
            cx = group_centers[gi]
            n = len(vals)

            if n < 4:
                # 数据太少，只画散点
                for v in vals:
                    jitter = (_random.random() - 0.5) * 0.2
                    px = cx + jitter * box_width
                    py = val_to_y(v)
                    canvas.create_oval(px - 2, py - 2, px + 2, py + 2,
                                       fill='black', outline='')
                continue

            # 计算箱线图统计量
            median = statistics.median(vals)
            q1_idx = n // 4
            q3_idx = 3 * n // 4
            q1 = vals[q1_idx]
            q3 = vals[q3_idx]
            iqr_val = q3 - q1
            lower_whisker = max(min(vals), q1 - 1.5 * iqr_val)
            upper_whisker = min(max(vals), q3 + 1.5 * iqr_val)

            y_q1 = val_to_y(q1)
            y_q3 = val_to_y(q3)
            y_median = val_to_y(median)
            y_lower = val_to_y(lower_whisker)
            y_upper = val_to_y(upper_whisker)

            box_left = cx - box_width
            box_right = cx + box_width

            # 箱体（白色填充，黑色边框）
            canvas.create_rectangle(box_left, y_q3, box_right, y_q1,
                                    fill='white', outline='black', width=1.5)

            # 中位线
            canvas.create_line(box_left, y_median, box_right, y_median,
                               fill='black', width=2)

            # 下须线
            canvas.create_line(cx, y_q1, cx, y_lower, fill='black', width=1.5)
            canvas.create_line(cx - box_width * 0.5, y_lower,
                               cx + box_width * 0.5, y_lower,
                               fill='black', width=1.5)

            # 上须线
            canvas.create_line(cx, y_q3, cx, y_upper, fill='black', width=1.5)
            canvas.create_line(cx - box_width * 0.5, y_upper,
                               cx + box_width * 0.5, y_upper,
                               fill='black', width=1.5)

            # 散点（黑色实心圆，带抖动）
            for v in vals:
                jitter = (_random.random() - 0.5) * 0.4 * box_width
                px = cx + jitter
                py = val_to_y(v)
                r = 2.5
                canvas.create_oval(px - r, py - r, px + r, py + r,
                                   fill='black', outline='', stipple='')

            # X轴标签
            canvas.create_text(cx, top_m + plot_h + 12,
                               text=person, font=('微软雅黑', 10), fill='#333')

            # 统计文本注释（每组上方）
            person_stats = next((s for s in (stats_data or []) if s['检验人'] == person), None)
            if person_stats:
                stat_lines = [
                    (person, True),
                    (f'最大值: {person_stats["最大值"]}', False),
                    (f'均值: {person_stats["均值"]:.5f}', False),
                    (f'最小值: {person_stats["最小值"]}', False),
                    (f'数目: {person_stats["数目"]}', False),
                ]
                stat_y_start = top_m - 28
                line_h = 14
                for li, (text, is_bold) in enumerate(stat_lines):
                    font_config = ('微软雅黑', 8, 'bold') if is_bold else ('微软雅黑', 8)
                    canvas.create_text(cx, stat_y_start - (len(stat_lines) - 1 - li) * line_h,
                                       text=text, font=font_config, fill='#222')

        # 图例（右上角）
        legend_x = left_m + plot_w - 100
        legend_y = top_m - 40
        # 黑色圆点图例
        canvas.create_oval(legend_x - 3, legend_y - 3, legend_x + 3, legend_y + 3,
                           fill='black', outline='')
        canvas.create_text(legend_x + 8, legend_y, text='测量值',
                           anchor='w', font=('微软雅黑', 8), fill='#333')
        legend_y += 18
        # 规格限图例
        if legend_items:
            for label, color, _ in legend_items:
                canvas.create_line(legend_x - 8, legend_y, legend_x + 8, legend_y,
                                   fill=color, dash=(4, 3), width=1.5)
                canvas.create_text(legend_x + 13, legend_y, text=f'{label}',
                                   anchor='w', font=('微软雅黑', 8), fill='#E74C3C')
                legend_y += 18

        # 标题（位于统计文本上方，紧挨最大值）
        canvas.create_text(left_m + plot_w / 2, top_m - 96,
                           text=f'{item_name if item_name else ""}',
                           font=('微软雅黑', 12, 'bold'), fill='#333')

        # X/Y轴标签
        canvas.create_text(left_m + plot_w / 2, top_m + plot_h + 38,
                           text='检验人', font=('微软雅黑', 10), fill='#333')
        canvas.create_text(left_m - 55, top_m + plot_h / 2,
                           text='测量值', font=('微软雅黑', 10), fill='#333', angle=90)

    # ==================== 正态分布图 ====================

    @staticmethod
    def _draw_normal_distribution(canvas):
        """在Canvas上绘制正态分布直方图+拟合曲线"""
        data = getattr(canvas, '_data', None)
        item_name = getattr(canvas, '_item_name', '')
        if not data or len(data) < 3:
            return

        canvas.delete('all')
        w = canvas.winfo_width()
        h = canvas.winfo_height()
        if w < 100 or h < 80:
            return

        import math as _math
        mean_val = statistics.mean(data)
        std_val = statistics.stdev(data) if len(data) > 1 else 1

        # 边距
        left_m = 70
        right_m = 30
        top_m = 40
        bottom_m = 50
        plot_w = w - left_m - right_m
        plot_h = h - top_m - bottom_m

        # 确定分箱
        n_bins = min(30, max(8, int(len(data) ** 0.5)))
        data_min = min(data)
        data_max = max(data)
        data_range = data_max - data_min
        if data_range < 0.001:
            data_range = 1.0
        margin = data_range * 0.05
        bin_edges = [data_min - margin + (data_range + 2 * margin) * i / n_bins
                      for i in range(n_bins + 1)]
        bin_counts = [0] * n_bins
        for v in data:
            for bi in range(n_bins):
                if bi == n_bins - 1:
                    if bin_edges[bi] <= v <= bin_edges[bi + 1]:
                        bin_counts[bi] += 1
                        break
                else:
                    if bin_edges[bi] <= v < bin_edges[bi + 1]:
                        bin_counts[bi] += 1
                        break

        max_count = max(bin_counts) if bin_counts else 1
        bar_w = plot_w / n_bins * 0.9

        # Y轴
        n_y_ticks = 5
        for i in range(n_y_ticks + 1):
            frac = i / n_y_ticks
            y = top_m + plot_h * (1 - frac)
            val = max_count * frac
            canvas.create_line(left_m - 4, y, left_m, y, fill='#666')
            canvas.create_text(left_m - 8, y, text=f'{int(val)}',
                               anchor='e', font=('Arial', 8), fill='#333')

        # 直方图
        for bi in range(n_bins):
            x = left_m + bi * (plot_w / n_bins) + (plot_w / n_bins - bar_w) / 2
            bar_h = (bin_counts[bi] / max_count) * plot_h if max_count > 0 else 0
            y_top = top_m + plot_h - bar_h
            canvas.create_rectangle(x, y_top, x + bar_w, top_m + plot_h,
                                    fill='#5B9BD5', outline='#4A8AC0', width=1)

        # 正态分布拟合曲线
        if std_val > 0:
            x_points = []
            y_points = []
            x_range_start = data_min - 3 * std_val
            x_range_end = data_max + 3 * std_val
            for i in range(200):
                x_val = x_range_start + (x_range_end - x_range_start) * i / 199
                pdf_val = (1 / (std_val * _math.sqrt(2 * _math.pi))) * \
                          _math.exp(-0.5 * ((x_val - mean_val) / std_val) ** 2)
                x_points.append(x_val)
                y_points.append(pdf_val)

            # 缩放曲线到直方图
            if y_points:
                max_pdf = max(y_points)
                if max_pdf > 0:
                    scale = (max_count / max_pdf) * (data_range / n_bins) if max_count > 0 else 1
                    curve_points = []
                    for i in range(len(x_points)):
                        px = left_m + (x_points[i] - (data_min - margin)) / \
                            (data_range + 2 * margin) * plot_w
                        py = top_m + plot_h - (y_points[i] * scale / max(max(bin_counts), 1)) * plot_h
                        curve_points.extend([px, py])
                    if len(curve_points) >= 4:
                        canvas.create_line(curve_points, fill='#C0392B', width=2, smooth=True)

        # 标注
        canvas.create_text(left_m + plot_w / 2, top_m - 15,
                           text=f'{item_name} - 正态分布 (μ={mean_val:.4f}, σ={std_val:.4f}, n={len(data)})',
                           font=('微软雅黑', 10, 'bold'), fill='#333')
        canvas.create_line(left_m, top_m + plot_h, left_m + plot_w, top_m + plot_h, fill='#666')

    # ==================== 控制图 ====================

    @staticmethod
    def _draw_control_chart(canvas):
        """在Canvas上绘制控制图（I-MR 单值移动极差图）"""
        data = getattr(canvas, '_data', None)
        item_name = getattr(canvas, '_item_name', '')
        if not data or len(data) < 3:
            return

        canvas.delete('all')
        w = canvas.winfo_width()
        h = canvas.winfo_height()
        if w < 100 or h < 80:
            return

        import math as _math
        n = len(data)
        mean_val = statistics.mean(data)

        # 计算移动极差
        mr_values = [abs(data[i] - data[i - 1]) for i in range(1, n)]
        mr_mean = statistics.mean(mr_values) if mr_values else 0

        # 控制限：I-MR chart
        # UCL = mean + 2.66 * MR_mean, LCL = mean - 2.66 * MR_mean
        ucl = mean_val + 2.66 * mr_mean
        lcl = mean_val - 2.66 * mr_mean

        # 边距
        left_m = 70
        right_m = 30
        top_m = 40
        bottom_m = 50
        plot_w = w - left_m - right_m
        plot_h = h - top_m - bottom_m

        all_vals = data + [ucl, lcl, mean_val]
        y_min = min(all_vals) - abs(min(all_vals)) * 0.1
        y_max = max(all_vals) + abs(max(all_vals)) * 0.1
        y_range = y_max - y_min
        if y_range < 0.001:
            y_range = 1.0

        def val_to_y(v):
            return top_m + plot_h - (v - y_min) / y_range * plot_h

        def idx_to_x(i):
            return left_m + i / max(n - 1, 1) * plot_w

        # Y轴刻度
        n_y_ticks = 5
        for i in range(n_y_ticks + 1):
            frac = i / n_y_ticks
            y = top_m + plot_h * (1 - frac)
            val = y_min + frac * y_range
            canvas.create_line(left_m - 4, y, left_m, y, fill='#666')
            canvas.create_text(left_m - 8, y, text=f'{val:.3f}',
                               anchor='e', font=('Arial', 7), fill='#333')

        # 控制限虚线
        for val, color, label in [(ucl, '#E74C3C', f'UCL={ucl:.4f}'),
                                    (lcl, '#E74C3C', f'LCL={lcl:.4f}'),
                                    (mean_val, '#2C3E50', f'CL={mean_val:.4f}')]:
            y = val_to_y(val)
            canvas.create_line(left_m, y, left_m + plot_w, y,
                               fill=color, dash=(6, 3), width=1.5)
            canvas.create_text(left_m + plot_w + 5, y, text=label,
                               anchor='w', font=('Arial', 7), fill=color)

        # 数据点连线
        points = []
        for i in range(n):
            px = idx_to_x(i)
            py = val_to_y(data[i])
            points.extend([px, py])
        if len(points) >= 4:
            canvas.create_line(points, fill='#5B9BD5', width=1.5)

        # 数据点
        for i in range(n):
            px = idx_to_x(i)
            py = val_to_y(data[i])
            r = 3
            color = '#E74C3C' if data[i] > ucl or data[i] < lcl else '#5B9BD5'
            canvas.create_oval(px - r, py - r, px + r, py + r,
                               fill=color, outline=color)

        # 超限标记
        out_indices = [i for i, v in enumerate(data) if v > ucl or v < lcl]
        if out_indices:
            canvas.create_text(left_m + plot_w / 2, top_m - 15,
                               text=f'超限点: {len(out_indices)}个 (位置: {out_indices[:10]})',
                               font=('Arial', 8), fill='#E74C3C')

        # X轴标签
        x_step = max(1, n // 15)
        for i in range(0, n, x_step):
            px = idx_to_x(i)
            canvas.create_text(px, top_m + plot_h + 8,
                               text=str(i + 1), font=('Arial', 7), fill='#666')

        canvas.create_text(left_m + plot_w / 2, top_m - 25,
                           text=f'{item_name} - 控制图 (I-MR)',
                           font=('微软雅黑', 10, 'bold'), fill='#333')

    # ==================== 导出 ====================

    def _export_results(self):
        filtered = self._get_filtered_anomalies()
        if not filtered:
            messagebox.showwarning('提示', '没有可导出的结果（当前筛选条件下）')
            return

        path = filedialog.asksaveasfilename(
            title='导出结果',
            defaultextension='.xlsx',
            filetypes=[('Excel 文件', '*.xlsx'), ('所有文件', '*.*')],
            initialfile=f'PQC分析结果_{datetime.now().strftime("%Y%m%d_%H%M%S")}.xlsx'
        )
        if not path:
            return

        try:
            grouped = defaultdict(list)
            for a in filtered:
                grouped[a['异常类型']].append(a)

            with pd.ExcelWriter(path, engine='openpyxl') as writer:
                for atype in ANOMALY_TYPES:
                    items = grouped.get(atype, [])
                    if not items:
                        continue

                    sheet_data = []
                    for a in items:
                        row = {
                            '异常类型': a['异常类型'],
                            '检验项目/SN': a['检验项目/SN'],
                            '检验人/站点': a['检验人/站点'],
                            '任务单/统计信息': a['任务单/统计信息'],
                            '详情': a['详情'],
                            '备注': a['备注'],
                        }
                        full_info = a.get('_full_info', {})
                        for k, v in full_info.items():
                            if isinstance(v, dict):
                                row[k] = json.dumps(v, ensure_ascii=False)
                            elif isinstance(v, list):
                                row[k] = ', '.join(str(x) for x in v)
                            else:
                                row[k] = v
                        sheet_data.append(row)

                    sheet_df = pd.DataFrame(sheet_data)
                    sheet_name = atype.replace('SN共用-', '').replace('数据异常-', '')[:31]
                    sheet_df.to_excel(writer, sheet_name=sheet_name, index=False)

                summary_data = []
                for a in filtered:
                    summary_data.append({
                        '异常类型': a['异常类型'],
                        '检验项目/SN': a['检验项目/SN'],
                        '检验人/站点': a['检验人/站点'],
                        '任务单/统计信息': a['任务单/统计信息'],
                        '详情': a['详情'],
                        '备注': a['备注'],
                    })
                summary_df = pd.DataFrame(summary_data)
                summary_df.to_excel(writer, sheet_name='全部异常汇总', index=False)

            self._log(f'结果已导出到: {path}（共 {len(filtered)} 条）')
            messagebox.showinfo('成功', f'已导出 {len(filtered)} 条记录到:\n{path}')
        except Exception as e:
            messagebox.showerror('错误', f'导出失败: {e}')


# ==================== 工具函数 ====================

def _to_numeric(val):
    """将测量值转为数值，非数值返回 NaN"""
    if pd.isna(val):
        return np.nan
    if isinstance(val, (int, float)):
        return float(val)
    s = str(val).strip()
    if s == '' or s.upper() in ('NA', 'N/A'):
        return np.nan
    try:
        return float(s)
    except ValueError:
        return np.nan


def _to_numeric_series(s):
    """向量化版本：整列转数值，非数值返回 NaN，结果与 _to_numeric 完全一致（float64）。"""
    return pd.to_numeric(s, errors='coerce').astype(float)


# ==================== 入口 ====================

def main():
    root = tk.Tk()
    PQCApp(root)
    root.mainloop()


if __name__ == '__main__':
    main()
