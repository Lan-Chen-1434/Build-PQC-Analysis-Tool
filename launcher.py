# -*- coding: utf-8 -*-
"""
PQC 数据分析工具 - 启动器

程序启动时先显示一个加载动画小窗口，
在后台线程加载主程序（pandas/numpy 等大依赖），
加载完成后关闭动画窗口并启动主界面。

跨平台线程安全说明：
  macOS 的 Tk(Aqua) 禁止在后台线程直接调用任何 Tk 接口
  （包括 root.after），否则事件会被吞掉导致界面卡死。
  因此后台线程只负责 import，结果经 queue 传给主线程，
  由主线程的定时器统一处理。Windows/macOS/Linux 均安全。
"""

import queue
import threading
import tkinter as tk
from tkinter import ttk, messagebox


class SplashScreen:
    """程序启动加载动画窗口（无边框、居中、置顶）"""

    WIDTH, HEIGHT = 400, 160
    BG = '#f5f6fa'
    GREEN = '#28a745'

    def __init__(self):
        self.root = tk.Tk()
        self.root.overrideredirect(True)  # 无边框
        self.root.attributes('-topmost', True)
        self.root.configure(bg=self.BG)
        self._closed = False

        # 居中显示
        sw = self.root.winfo_screenwidth()
        sh = self.root.winfo_screenheight()
        x = (sw - self.WIDTH) // 2
        y = (sh - self.HEIGHT) // 2
        self.root.geometry(f'{self.WIDTH}x{self.HEIGHT}+{x}+{y}')

        # 细边框 + 内容区
        outer = tk.Frame(self.root, bg='#c8ccd2')
        outer.pack(fill=tk.BOTH, expand=True)
        inner = tk.Frame(outer, bg=self.BG)
        inner.pack(fill=tk.BOTH, expand=True, padx=1, pady=1)

        tk.Label(inner, text='PQC 数据分析', bg=self.BG, fg='#333333',
                 font=('微软雅黑', 14, 'bold')).pack(pady=(24, 4))

        self.dots_var = tk.StringVar(value='正在加载')
        tk.Label(inner, textvariable=self.dots_var, bg=self.BG, fg='#777777',
                 font=('微软雅黑', 10)).pack(pady=(0, 12))

        # 绿色滚动进度条：Windows 借用 clam 元素染绿；
        # macOS 的 Aqua 原生主题不支持自定义 clam 元素，用系统默认样式
        import platform
        style = ttk.Style(self.root)
        bar_style = 'TProgressbar'
        if platform.system() != 'Darwin':
            try:
                style.element_create('green.pbar', 'from', 'clam')
                style.layout('green.Horizontal.TProgressbar', [
                    ('Horizontal.Progressbar.trough', {
                        'children': [('green.pbar', {'side': 'left', 'sticky': 'ns'})],
                        'sticky': 'nswe',
                    }),
                ])
            except tk.TclError:
                pass  # 元素已存在则复用
            style.configure('green.Horizontal.TProgressbar',
                            background=self.GREEN, troughcolor='#e3e5e8')
            bar_style = 'green.Horizontal.TProgressbar'
        self.bar = ttk.Progressbar(inner, style=bar_style,
                                   mode='indeterminate', length=300)
        self.bar.pack(pady=(0, 20))
        self.bar.start(12)

        self._dots_count = 0
        self._after_id = None
        self._animate_dots()

    def _animate_dots(self):
        """省略号循环动画：正在加载. → .. → ..."""
        if self._closed:
            return
        self._dots_count = (self._dots_count + 1) % 4
        try:
            self.dots_var.set('正在加载' + '.' * self._dots_count)
            self._after_id = self.root.after(400, self._animate_dots)
        except tk.TclError:
            pass

    def close(self):
        self._closed = True
        try:
            if self._after_id is not None:
                self.root.after_cancel(self._after_id)
                self._after_id = None
            self.bar.stop()
            self.root.destroy()
        except tk.TclError:
            pass

    def mainloop(self):
        self.root.mainloop()


def main():
    splash = SplashScreen()
    ui_queue = queue.Queue()  # 后台线程 → 主线程 的安全通道

    def _load_main_app():
        """后台线程：只做 import，不碰任何 Tk 接口"""
        try:
            import pqc_analysis  # 重依赖（pandas/numpy）在此加载
            ui_queue.put(('ok', pqc_analysis))
        except Exception as e:
            ui_queue.put(('err', e))

    def _poll_queue():
        """主线程定时器：检查后台加载结果"""
        try:
            kind, payload = ui_queue.get_nowait()
        except queue.Empty:
            splash.root.after(100, _poll_queue)
            return

        if kind == 'ok':
            splash.close()
            payload.main()  # 启动主界面
        else:
            splash.close()
            messagebox.showerror('启动失败', f'程序加载失败:\n{payload}')

    threading.Thread(target=_load_main_app, daemon=True).start()
    splash.root.after(100, _poll_queue)
    splash.mainloop()


if __name__ == '__main__':
    main()
