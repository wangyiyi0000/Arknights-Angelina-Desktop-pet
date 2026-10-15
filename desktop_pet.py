# -*- coding: utf-8 -*-
"""
桌面宠物（天选姬风格）

一个使用 PyQt5 实现的桌面宠物程序，支持：
- 无边框、透明背景、窗口置顶（200x200，初始位于屏幕右下角）
- 十种状态对应十张 GIF 动画，默认启动为“坐坐”
- 待机模式：每 10 分钟自动随机切换状态
- 左键拖拽移动窗口；左键单击弹出橙色对话气泡（3 秒后消失）
- 右键弹出菜单：主菜单 / 状态选择 / 散步模式
- 散步模式：上下左右四方向等概率随机移动，每个方向持续一段时间后自动换向
- 最小化到系统托盘，托盘菜单支持显示/隐藏、退出
- 主菜单支持开关“开机自启”（写入当前用户注册表 Run 项）
- “我想听歌”：自动检测音乐软件路径，找不到可手动填写，跳过则打开网页版网易云
- “开始放歌！”：随机播放“夏日活动主题曲”文件夹里的歌曲
- 桌宠左侧五条音频电平条：识别电脑声音；听到其他系统声音持续 3 秒后自动切“看书”
  （点击桌宠自己播放的语音不会触发状态切换）

目录结构：
    desktop_pet.py
    gifs/购物.gif
    gifs/海边.gif
    gifs/看书.gif
    gifs/拍照.gif
    gifs/骑行.gif
    gifs/潜水.gif
    gifs/送货.gif
    gifs/探险.gif
    gifs/纸飞机.gif
    gifs/坐坐.gif
    texts/请输入文本.txt       （对话气泡文字，可自行添加/修改 .txt）
    audio/                    （音频文件夹，放入 mp3/wav 后点击气泡会随机播放）
    语音包和文字/任命助理.txt   （语音包文字，与同名 .wav 配对）
    语音包和文字/任命助理.wav   （对应语音，点击气泡时文字与语音一起播放）

运行前安装依赖：
    pip install PyQt5
"""

import json
import os
import random
import subprocess
import sys
import threading
import time
import traceback
import webbrowser
import winreg

from PyQt5.QtCore import QPoint, QPointF, QRect, QRectF, QSize, Qt, QTimer, QUrl
from PyQt5.QtGui import (QBrush, QColor, QFont, QFontMetrics, QIcon, QMovie,
                         QPainter, QPainterPath, QPixmap, QPolygonF, QTransform)
from PyQt5.QtWidgets import (QApplication, QDialog, QLabel, QMenu,
                             QFileDialog, QHBoxLayout, QLineEdit, QMessageBox,
                             QPushButton, QSlider, QSpinBox, QSystemTrayIcon,
                             QVBoxLayout, QWidget)

# ------------------------------ 常量配置 ------------------------------

WINDOW_SIZE = 200          # 桌宠窗口尺寸（像素）
SCREEN_MARGIN = 20         # 窗口与屏幕边缘的间距
PET_SCALE_MIN = 0.5        # 桌宠大小可调范围：最小 50%
PET_SCALE_MAX = 2.0        # 桌宠大小可调范围：最大 200%

BUBBLE_TEXT = "请输入文本"  # 对话气泡默认文字（texts 文件夹为空时使用）
BUBBLE_FONT_SIZE = 11      # 气泡文字基础字号（随桌宠大小等比缩放）
BUBBLE_MIN_WIDTH = 170     # 气泡最小宽度
BUBBLE_MAX_WIDTH = 360     # 气泡最大宽度（超过后自动换行）
BUBBLE_MIN_HEIGHT = 56     # 气泡最小高度
BUBBLE_PADDING_X = 16      # 气泡左右内边距
BUBBLE_PADDING_Y = 12      # 气泡上下内边距
BUBBLE_BLANK_LINES = 1     # 文字上下各额外留空的行数（呼吸空间）
TRIANGLE_SIZE = 12         # 气泡下方三角形指示器大小
BUBBLE_DURATION_MS = 3000  # 气泡显示时长（3 秒）
FOLLOW_INTERVAL_MS = 16    # 气泡跟随刷新间隔（约 60 帧/秒）
FOLLOW_SMOOTHNESS = 0.2    # 气泡每次跟随接近目标的比例（0~1，越小越平滑）

IDLE_INTERVAL_MS = 600000  # 待机状态切换间隔（10 分钟）
WALK_INTERVAL_MS = 150         # 散步模式移动间隔（毫秒），越小速度越快
WALK_MIN_STEP = 5              # 每步移动的最小像素（幅度）
WALK_MAX_STEP = 10             # 每步移动的最大像素（幅度）
WALK_DIRECTION_MIN_MS = 30000  # 每个方向至少持续的时间（30 秒）
WALK_DIRECTION_MAX_MS = 60000  # 每个方向最长持续的时间（60 秒）

ORANGE = QColor("#FF8C00")  # 气泡 / 主题色（橙色）

# 状态 -> GIF 文件映射（列表顺序即菜单顺序）
STATES = [
    ("购物", "购物.gif"),
    ("海边", "海边.gif"),
    ("看书", "看书.gif"),
    ("拍照", "拍照.gif"),
    ("骑行", "骑行.gif"),
    ("潜水", "潜水.gif"),
    ("送货", "送货.gif"),
    ("探险", "探险.gif"),
    ("纸飞机", "纸飞机.gif"),
    ("坐坐", "坐坐.gif"),
]

# 散步模式专用的移动动作（仅出现在散步模式，不参与待机随机切换）
# 左右移动：送货 / 纸飞机 / 骑行（按朝向水平镜像）；上下移动：潜水
WALK_HORIZONTAL_STATES = ["送货", "纸飞机", "骑行"]
WALK_STATES = WALK_HORIZONTAL_STATES + ["潜水"]

STATE_TO_GIF = dict(STATES)
DEFAULT_STATE = "坐坐"

# 脚本所在目录，GIF 存放在同目录的 gifs 文件夹中
if getattr(sys, "frozen", False):
    # 打包成 exe 后，以 exe 所在目录为准，gifs 文件夹放在 exe 旁边
    BASE_DIR = os.path.dirname(sys.executable)
else:
    BASE_DIR = os.path.dirname(os.path.abspath(__file__))
GIF_DIR = os.path.join(BASE_DIR, "gifs")
TEXT_DIR = os.path.join(BASE_DIR, "texts")
AUDIO_DIR = os.path.join(BASE_DIR, "audio")
VOICE_DIR = os.path.join(BASE_DIR, "语音包和文字")
UI_DIR = os.path.join(BASE_DIR, "ui")
MUSIC_CONFIG_FILE = os.path.join(BASE_DIR, "music_config.json")  # 音乐软件路径配置
SETTINGS_FILE = os.path.join(BASE_DIR, "settings.json")  # 桌宠设置持久化
SONGS_DIR = os.path.join(BASE_DIR, "夏日活动主题曲")  # 歌曲文件夹

# 音频文件夹中支持的文件格式（点击气泡时随机播放）
AUDIO_EXTS = (".mp3", ".wav", ".m4a", ".ogg", ".flac")

# 气泡装饰：样式一（1、2 号图片放在左右上角），样式二（3-7 号图片半透明随机贴纸）
DECO1_MAX_SIZE = 48   # 样式一角标装饰的最大尺寸
DECO2_MAX_SIZE = 36   # 样式二贴纸的最大尺寸
DECO2_OPACITY = 0.7   # 样式二贴纸透明度（0~1，越小越透明）

# 音频电平（五条竖条 + 声音检测）
METER_BAR_COUNT = 5          # 竖直长条数量
METER_BAR_WIDTH = 10         # 单条宽度
METER_BAR_GAP = 4            # 条间距
METER_MARGIN = 6             # 四周留白
METER_HEIGHT = 96            # 电平条总高度
METER_SOUND_THRESHOLD = 0.02 # 判定“有声音”的音量阈值
METER_SOUND_TRIGGER_MS = 3000  # 外部声音持续多久后切到看书状态
METER_SILENT_RESTORE_MS = 2000  # 静音多久后恢复原状态
AUDIO_POLL_MS = 100          # 声音检测 / 状态刷新间隔
AUDIO_SAMPLE_RATE = 16000    # 回环采集采样率
AUDIO_BLOCKSIZE = 1024       # 每次采集的帧数
AUDIO_RMS_GAIN = 3.0         # RMS 到 0~1 电平的放大倍数
AUDIO_DEBUG_LOG = os.path.join(BASE_DIR, "audio_debug.log")  # 音频调试日志

# 音乐控制面板
MUSIC_PANEL_WIDTH = 150   # 面板基础宽度
MUSIC_PANEL_HEIGHT = 92   # 面板基础高度
MCI_POLL_MS = 200         # MCI 播放进度轮询间隔

# 快速点击彩蛋
RAPID_CLICK_INTERVAL = 0.5  # 相邻两次点击间隔小于 0.5 秒视为快速连点
RAPID_CLICK_COUNT = 10      # 连续快速点击达到该次数弹出彩蛋图片
RAPID_EGG_DURATION_MS = 7000  # 彩蛋图片显示时长（7 秒后自动关闭）


def available_screen_geometry():
    """获取主屏幕的可用区域（兼容部分平台 primaryScreen 为空的情况）。"""
    screen = QApplication.primaryScreen()
    if screen is not None:
        return screen.availableGeometry()
    return QApplication.desktop().availableGeometry()


# ---------------------------- 开机自启 ----------------------------

AUTOSTART_RUN_KEY = r"Software\Microsoft\Windows\CurrentVersion\Run"
AUTOSTART_VALUE_NAME = "桌宠"


def _autostart_command():
    """构造开机自启的命令行：打包成 exe 用 exe 路径，源码运行用 python 命令。"""
    if getattr(sys, "frozen", False):
        return '"%s"' % sys.executable
    return '"%s" "%s"' % (sys.executable, os.path.abspath(__file__))


def is_autostart_enabled():
    """检查当前用户的开机自启是否已开启。"""
    try:
        key = winreg.OpenKey(winreg.HKEY_CURRENT_USER, AUTOSTART_RUN_KEY,
                             0, winreg.KEY_READ)
        try:
            winreg.QueryValueEx(key, AUTOSTART_VALUE_NAME)
            return True
        finally:
            key.Close()
    except FileNotFoundError:
        return False
    except OSError as exc:
        print("[警告] 读取开机自启状态失败：", exc)
        return False


def set_autostart(enabled):
    """开启/关闭开机自启（写入/删除当前用户注册表 Run 项），返回是否成功。"""
    try:
        if enabled:
            key = winreg.CreateKey(winreg.HKEY_CURRENT_USER, AUTOSTART_RUN_KEY)
            try:
                winreg.SetValueEx(key, AUTOSTART_VALUE_NAME, 0,
                                  winreg.REG_SZ, _autostart_command())
            finally:
                key.Close()
        else:
            try:
                key = winreg.OpenKey(winreg.HKEY_CURRENT_USER, AUTOSTART_RUN_KEY,
                                     0, winreg.KEY_SET_VALUE)
                try:
                    winreg.DeleteValue(key, AUTOSTART_VALUE_NAME)
                finally:
                    key.Close()
            except FileNotFoundError:
                pass  # 本来就未开启，无需处理
        return True
    except OSError as exc:
        print("[警告] 设置开机自启失败：", exc)
        return False


class BubbleWidget(QWidget):
    """橙色对话气泡：白色文字 + 底部三角形指示器，3 秒后自动消失，可平滑跟随桌宠。"""

    def __init__(self, text, pet, ui_images=None, scale=1.0, parent=None):
        super().__init__(parent)
        self._text = text
        self._pet = pet  # 用于跟随桌宠位置
        self._ui_images = ui_images or {}  # {编号: QPixmap}，来自 ui 文件夹
        self._scale = max(PET_SCALE_MIN, min(PET_SCALE_MAX, scale))  # 缩放系数
        self._deco_style = None   # 本次气泡装饰形式（1 或 2）
        self._deco_rects = []     # 样式二：[(图片编号, 位置矩形)]，保证不重叠
        self._above_pet = True    # 气泡显示在桌宠上方（否则显示在下方）
        # 独立顶层窗口，透明、无边框、置顶
        self.setWindowFlags(Qt.FramelessWindowHint
                            | Qt.WindowStaysOnTopHint
                            | Qt.Tool)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self._apply_font()
        self._resize_for_text(self._text)

        self._hide_timer = QTimer(self)
        self._hide_timer.setSingleShot(True)
        self._hide_timer.timeout.connect(self.hide)
        self._hide_timer.start(BUBBLE_DURATION_MS)

        # 跟随定时器：按固定频率把气泡往桌宠上方目标位置平滑推进
        self._follow_timer = QTimer(self)
        self._follow_timer.setInterval(FOLLOW_INTERVAL_MS)
        self._follow_timer.timeout.connect(self._follow_tick)

    def _apply_font(self):
        """按缩放系数设置气泡字体（文字随桌宠大小等比缩放）。"""
        font = QFont("Microsoft YaHei")
        font.setPointSizeF(BUBBLE_FONT_SIZE * self._scale)
        self.setFont(font)

    def _s(self, value):
        """按缩放系数换算尺寸（至少 1 像素）。"""
        return max(1, int(round(value * self._scale)))

    def set_scale(self, scale):
        """整体调整气泡缩放（尺寸、字体、装饰等比变化）。"""
        scale = max(PET_SCALE_MIN, min(PET_SCALE_MAX, scale))
        if abs(scale - self._scale) < 0.01:
            return
        self._scale = scale
        self._apply_font()
        self._resize_for_text(self._text)
        if self._deco_style == 2:
            self._deco_rects = self._random_deco_rects()
        self.update()
        if self.isVisible():
            self.start_follow()

    def set_text(self, text):
        """更新气泡文字，并按文字长度重新调整气泡大小。"""
        self._text = text
        self._resize_for_text(text)
        self.update()

    def set_duration(self, duration_ms):
        """按音频时长设置气泡显示时间并重新计时。"""
        if duration_ms and duration_ms > 0:
            self._hide_timer.start(duration_ms)

    def _resize_for_text(self, text):
        """按文字长度折行并动态计算气泡尺寸，测量与渲染使用同一套折行结果。"""
        font_metrics = QFontMetrics(self.font())
        max_text_width = self._s(BUBBLE_MAX_WIDTH) - 2 * self._s(BUBBLE_PADDING_X)
        self._text_lines = self._wrap_text(text, max_text_width)
        max_line_width = max(
            (font_metrics.horizontalAdvance(line) for line in self._text_lines),
            default=0,
        )
        body_width = max(
            self._s(BUBBLE_MIN_WIDTH),
            min(self._s(BUBBLE_MAX_WIDTH),
                max_line_width + 2 * self._s(BUBBLE_PADDING_X)),
        )
        body_height = max(
            self._s(BUBBLE_MIN_HEIGHT),
            (len(self._text_lines) + 2 * BUBBLE_BLANK_LINES)
            * font_metrics.lineSpacing()
            + 2 * self._s(BUBBLE_PADDING_Y),
        )
        self.setFixedSize(body_width, body_height + self._s(TRIANGLE_SIZE))

    def _wrap_text(self, text, max_width):
        """按字符宽度把文字折成多行（中文等无空格文字也能正确换行）。"""
        font_metrics = QFontMetrics(self.font())
        lines = []
        current = ""
        for ch in text:
            trial = current + ch
            if current and font_metrics.horizontalAdvance(trial) > max_width:
                lines.append(current)
                current = ch
            else:
                current = trial
        if current:
            lines.append(current)
        return lines

    def _body_rect(self):
        """气泡主体区域（根据气泡在桌宠上方/下方，给三角形指示器留出空间）。"""
        triangle = self._s(TRIANGLE_SIZE)
        if self._above_pet:
            return QRect(0, 0, self.width(), self.height() - triangle)
        return QRect(0, triangle, self.width(), self.height() - triangle)

    def _compute_target(self, pet_rect):
        """计算气泡位置：优先桌宠上方居中；上方放不下时放到下方，避免遮挡桌宠。"""
        screen = available_screen_geometry()
        x = pet_rect.center().x() - self.width() // 2
        above_y = pet_rect.top() - self.height() + 1   # 三角形尖端贴近桌宠顶部
        below_y = pet_rect.bottom() + 2                # 桌宠下方留 2 像素间距
        if above_y >= screen.top() + 4:
            self._above_pet = True
            y = above_y
        else:
            # 上方空间不足：放到桌宠下方，三角形朝上指向桌宠
            self._above_pet = False
            y = below_y
        x = max(screen.left() + 4, min(x, screen.right() - self.width() - 4))
        y = max(screen.top() + 4, min(y, screen.bottom() - self.height() - 4))
        return QPoint(x, y)

    def start_follow(self):
        """开始跟随桌宠移动（气泡可见时生效）。"""
        if self.isVisible() and not self._follow_timer.isActive():
            self._follow_timer.start()

    def stop_follow(self):
        """停止跟随。"""
        self._follow_timer.stop()

    def _follow_tick(self):
        """每帧把气泡往目标位置推进一点，形成平滑跟随效果。"""
        if self._pet is None or not self._pet.isVisible():
            self.stop_follow()
            return
        target = self._compute_target(self._pet.frameGeometry())
        pos = self.pos()
        dx = target.x() - pos.x()
        dy = target.y() - pos.y()
        if abs(dx) <= 1 and abs(dy) <= 1:
            self.move(target)
            return

        def _step(delta):
            """计算单帧推进量：四舍五入且保证每帧至少推进 1 像素。"""
            if delta > 0:
                return max(1, int(round(delta * FOLLOW_SMOOTHNESS)))
            if delta < 0:
                return min(-1, int(round(delta * FOLLOW_SMOOTHNESS)))
            return 0

        self.move(QPoint(
            pos.x() + _step(dx),
            pos.y() + _step(dy),
        ))

    def paintEvent(self, event):
        """绘制圆角气泡主体和指向桌宠的三角形指示器。"""
        painter = QPainter(self)
        painter.setRenderHint(QPainter.Antialiasing)

        # 气泡主体尺寸随文字自适应
        body_width = self.width()
        triangle = self._s(TRIANGLE_SIZE)
        body_height = self.height() - triangle
        path = QPainterPath()
        # 注意：QPainterPath.addRoundedRect 只接受 QRectF（PyQt5 限制）
        if self._above_pet:
            # 气泡在桌宠上方：主体在上，三角形在底部朝下
            body = QRect(0, 0, body_width, body_height)
            triangle = QPolygonF([
                QPointF(body_width // 2 - triangle, body_height - 1),
                QPointF(body_width // 2 + triangle, body_height - 1),
                QPointF(body_width // 2, body_height + triangle - 1),
            ])
        else:
            # 气泡在桌宠下方：主体在下，三角形在顶部朝上
            body = QRect(0, triangle, body_width, body_height)
            triangle = QPolygonF([
                QPointF(body_width // 2 - triangle, triangle),
                QPointF(body_width // 2 + triangle, triangle),
                QPointF(body_width // 2, 1),
            ])
        path.addRoundedRect(QRectF(body), self._s(10), self._s(10))
        # 注意：QPainterPath.addPolygon 只接受 QPolygonF（PyQt5 限制）
        path.addPolygon(triangle)

        painter.fillPath(path, QBrush(ORANGE))

        # 装饰图片（先画装饰再画文字，保证文字可读）
        if self._deco_style == 1:
            self._draw_corner_decos(painter)
        elif self._deco_style == 2:
            self._draw_sticker_decos(painter)

        painter.setPen(Qt.white)
        # 按折行结果逐行居中绘制，保证文字完整显示
        font_metrics = QFontMetrics(self.font())
        line_height = font_metrics.lineSpacing()
        total_height = line_height * len(self._text_lines)
        # 注意：drawText 会把基线放在 y + ascent 处，
        # 因此这里不要再加 ascent，否则上方会多出一行空档，导致上下不对称
        # 再补偿半个 leading，使字形上下留白光学居中
        y = body.top() + (body.height() - total_height) // 2 + font_metrics.leading() // 2
        for line in self._text_lines:
            painter.drawText(body.left(), y, body.width(), line_height,
                             Qt.AlignHCenter, line)
            y += line_height
        painter.end()

    def show_above(self, pet_rect):
        """将气泡显示在桌宠窗口上方居中，并重新计时 3 秒。"""
        target = self._compute_target(pet_rect)  # 先确定在上方还是下方
        self._pick_decoration()  # 每次显示时随机选择装饰形式
        self.move(target)
        self.show()
        self.raise_()
        self._hide_timer.start(BUBBLE_DURATION_MS)
        self.start_follow()

    # ------------------------- 装饰图片 -------------------------

    def _pick_decoration(self):
        """随机选择装饰形式：样式一（角标）或样式二（半透明随机贴纸）。"""
        self._deco_style = None
        self._deco_rects = []
        has_style1 = all(i in self._ui_images for i in (1, 2))
        has_style2 = all(i in self._ui_images for i in (3, 4, 5, 6, 7))
        choices = []
        if has_style1:
            choices.append(1)
        if has_style2:
            choices.append(2)
        if not choices:
            return  # ui 图片不齐时不做装饰
        self._deco_style = random.choice(choices)
        if self._deco_style == 2:
            self._deco_rects = self._random_deco_rects()

    def _fit_size(self, pix, box):
        """保持宽高比缩放到 box 尺寸内，返回 (宽, 高)。"""
        if pix.width() <= box and pix.height() <= box:
            return pix.width(), pix.height()
        scaled = pix.scaled(box, box, Qt.KeepAspectRatio, Qt.SmoothTransformation)
        return scaled.width(), scaled.height()

    def _random_deco_rects(self):
        """样式二：把气泡分成若干格子，5 张图片随机分配到不同格子的随机位置，保证不重叠。"""
        body = self._body_rect()
        margin = self._s(6)
        cols, rows = 3, 2  # 3x2 共 6 个格子，5 张图各占一格
        cell_w = (body.width() - 2 * margin) // cols
        cell_h = (body.height() - 2 * margin) // rows
        size = min(self._s(DECO2_MAX_SIZE),
                   max(self._s(16), min(cell_w, cell_h) - self._s(8)))

        cells = [(col, row) for col in range(cols) for row in range(rows)]
        random.shuffle(cells)  # 随机决定每张图用哪个格子
        rects = []  # [(编号, QRect)]
        for idx in (3, 4, 5, 6, 7):
            pix = self._ui_images.get(idx)
            if pix is None:
                continue
            w, h = self._fit_size(pix, size)
            col, row = cells[len(rects)]
            area = QRect(body.left() + margin + col * cell_w,
                         body.top() + margin + row * cell_h,
                         cell_w, cell_h)
            x = random.randint(area.left(), max(area.left(), area.right() - w))
            y = random.randint(area.top(), max(area.top(), area.bottom() - h))
            rects.append((idx, QRect(x, y, w, h)))
        return rects

    def _draw_corner_decos(self, painter):
        """样式一：1 号图在右上角，2 号图在左上角。"""
        body = self._body_rect()
        margin = self._s(6)
        size = min(self._s(DECO1_MAX_SIZE),
                   max(self._s(24), body.height() // 2))
        for idx, align in ((1, Qt.AlignRight), (2, Qt.AlignLeft)):
            pix = self._ui_images.get(idx)
            if pix is None:
                continue
            scaled = pix.scaled(size, size, Qt.KeepAspectRatio, Qt.SmoothTransformation)
            if align == Qt.AlignRight:
                x = body.right() - margin - scaled.width()
            else:
                x = body.left() + margin
            y = body.top() + margin
            painter.drawPixmap(x, y, scaled)

    def _draw_sticker_decos(self, painter):
        """样式二：3-7 号图片降低透明度，画在随机且不重叠的位置。"""
        painter.setOpacity(DECO2_OPACITY)
        for idx, rect in self._deco_rects:
            pix = self._ui_images.get(idx)
            if pix is None:
                continue
            scaled = pix.scaled(rect.width(), rect.height(),
                                Qt.KeepAspectRatio, Qt.SmoothTransformation)
            painter.drawPixmap(rect.topLeft(), scaled)
        painter.setOpacity(1.0)

    def hideEvent(self, event):
        """隐藏时同时停止跟随，避免后台空转。"""
        self.stop_follow()
        super().hideEvent(event)


class AudioLevelMeter(QWidget):
    """桌宠左侧的五条音频电平条：根据系统声音大小点亮，支持随桌宠大小缩放。"""

    def __init__(self, pet, parent=None):
        super().__init__(parent)
        self._pet = pet
        self._levels = [0.0] * METER_BAR_COUNT  # 各条当前显示高度（0~1）
        self._scale = max(PET_SCALE_MIN, min(PET_SCALE_MAX, pet.pet_scale))
        # 独立顶层窗口，透明、无边框、置顶
        self.setWindowFlags(Qt.FramelessWindowHint
                            | Qt.WindowStaysOnTopHint
                            | Qt.Tool)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self._apply_size()

        self._timer = QTimer(self)
        self._timer.setInterval(50)
        self._timer.timeout.connect(self._refresh_levels)
        self._timer.start()

    def _s(self, value):
        """按缩放系数换算尺寸。"""
        return max(1, int(round(value * self._scale)))

    def _apply_size(self):
        """按缩放系数计算整体尺寸。"""
        width = (self._s(METER_MARGIN) * 2
                 + METER_BAR_COUNT * self._s(METER_BAR_WIDTH)
                 + (METER_BAR_COUNT - 1) * self._s(METER_BAR_GAP))
        self.setFixedSize(width, self._s(METER_HEIGHT))

    def set_scale(self, scale):
        """随桌宠大小一起等比缩放。"""
        scale = max(PET_SCALE_MIN, min(PET_SCALE_MAX, scale))
        if abs(scale - self._scale) < 0.01:
            return
        self._scale = scale
        self._apply_size()
        self.update()

    def _refresh_levels(self):
        """按系统音量平滑点亮五条竖条（低音高亮少，高音全亮）。"""
        level = max(0.0, min(1.0, self._pet.audio_level))
        for i in range(METER_BAR_COUNT):
            target = max(0.0, min(1.0, level * METER_BAR_COUNT - i))
            current = self._levels[i]
            new_value = current + (target - current) * 0.35
            self._levels[i] = new_value if abs(target - current) >= 0.01 else target
        self.update()

    def paintEvent(self, event):
        """绘制五条竖直长条：灰色底槽 + 橙色点亮部分。"""
        painter = QPainter(self)
        painter.setRenderHint(QPainter.Antialiasing)
        margin = self._s(METER_MARGIN)
        bar_width = self._s(METER_BAR_WIDTH)
        gap = self._s(METER_BAR_GAP)
        radius = self._s(4)
        max_h = self.height() - margin * 2 - self._s(6)
        for i in range(METER_BAR_COUNT):
            x = margin + i * (bar_width + gap)
            track = QRectF(x, margin + self._s(2), bar_width, max_h)
            # 底槽：微透明橙色
            painter.setPen(Qt.NoPen)
            painter.setBrush(QColor(255, 140, 0, 40))
            painter.drawRoundedRect(track, radius, radius)
            # 点亮部分：自底向上
            lit_h = max(self._s(3), max_h * self._levels[i])
            lit = QRectF(x, track.bottom() - lit_h, bar_width, lit_h)
            painter.setBrush(ORANGE)
            painter.drawRoundedRect(lit, radius, radius)
        painter.end()


class MusicPlayerPanel(QWidget):
    """桌宠右侧的音乐控制面板：上一首 / 播放暂停 / 下一首 / 进度条（图形按钮）。"""

    def __init__(self, pet, parent=None):
        super().__init__(parent)
        self._pet = pet
        self._scale = max(PET_SCALE_MIN, min(PET_SCALE_MAX, pet.pet_scale))
        # 独立顶层窗口，透明、无边框、置顶
        self.setWindowFlags(Qt.FramelessWindowHint
                            | Qt.WindowStaysOnTopHint
                            | Qt.Tool)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self._build_ui()
        self._apply_style()
        self._apply_size()

    def _s(self, value):
        """按缩放系数换算尺寸。"""
        return max(1, int(round(value * self._scale)))

    def _apply_font(self):
        font = QFont("Microsoft YaHei")
        font.setPointSizeF(9 * self._scale)
        self.setFont(font)

    def _build_ui(self):
        self._apply_font()
        layout = QVBoxLayout(self)
        layout.setContentsMargins(self._s(8), self._s(6),
                                  self._s(8), self._s(6))
        layout.setSpacing(self._s(4))

        self.title_label = QLabel("未播放")
        self.title_label.setAlignment(Qt.AlignCenter)
        layout.addWidget(self.title_label)

        self.slider = QSlider(Qt.Horizontal)
        self.slider.setRange(0, 0)
        self.slider.sliderReleased.connect(self._seek)
        layout.addWidget(self.slider)

        button_row = QHBoxLayout()
        button_row.setSpacing(self._s(6))
        self.prev_button = QPushButton()
        self.play_button = QPushButton()
        self.next_button = QPushButton()
        for button in (self.prev_button, self.play_button, self.next_button):
            button_row.addWidget(button)
        layout.addLayout(button_row)

        self.prev_button.clicked.connect(self._pet.play_previous)
        self.play_button.clicked.connect(self._pet.toggle_play_pause)
        self.next_button.clicked.connect(self._pet.play_next)
        self._apply_icons()

    def _apply_icons(self):
        """按当前缩放系数重新生成按钮图标（随桌宠大小等比缩放）。"""
        size = self._s(18)
        self.play_icon = self._make_icon("play")
        self.pause_icon = self._make_icon("pause")
        self.prev_button.setIcon(self._make_icon("prev"))
        self.next_button.setIcon(self._make_icon("next"))
        self.play_button.setIcon(self.play_icon)
        for button in (self.prev_button, self.play_button, self.next_button):
            button.setIconSize(QSize(size, size))

    def _make_icon(self, kind):
        """用 QPainter 绘制播放/暂停/上一首/下一首图标。"""
        size = self._s(18)
        pixmap = QPixmap(size, size)
        pixmap.fill(Qt.transparent)
        painter = QPainter(pixmap)
        painter.setRenderHint(QPainter.Antialiasing)
        painter.setPen(Qt.NoPen)
        painter.setBrush(QColor("white"))
        s = float(size)
        if kind == "play":
            painter.drawPolygon(QPolygonF([
                QPointF(s * 0.25, s * 0.15),
                QPointF(s * 0.85, s * 0.50),
                QPointF(s * 0.25, s * 0.85),
            ]))
        elif kind == "pause":
            painter.drawRoundedRect(QRectF(s * 0.24, s * 0.18, s * 0.18, s * 0.64),
                                    s * 0.03, s * 0.03)
            painter.drawRoundedRect(QRectF(s * 0.58, s * 0.18, s * 0.18, s * 0.64),
                                    s * 0.03, s * 0.03)
        elif kind == "prev":
            painter.drawRect(QRectF(s * 0.16, s * 0.20, s * 0.12, s * 0.60))
            painter.drawPolygon(QPolygonF([
                QPointF(s * 0.30, s * 0.50),
                QPointF(s * 0.86, s * 0.14),
                QPointF(s * 0.86, s * 0.86),
            ]))
        elif kind == "next":
            painter.drawPolygon(QPolygonF([
                QPointF(s * 0.14, s * 0.14),
                QPointF(s * 0.14, s * 0.86),
                QPointF(s * 0.70, s * 0.50),
            ]))
            painter.drawRect(QRectF(s * 0.72, s * 0.20, s * 0.12, s * 0.60))
        painter.end()
        return QIcon(pixmap)

    def _apply_style(self):
        """按缩放系数设置面板与子控件样式。"""
        self.setStyleSheet(
            "MusicPlayerPanel { background-color: rgba(30, 30, 30, 200);"
            " border-radius: %dpx; }" % self._s(10))
        self.title_label.setStyleSheet(
            "color: white; background: transparent; border: none;")
        self.slider.setStyleSheet(
            "QSlider::groove:horizontal { height: %dpx; background: #555555;"
            " border-radius: %dpx; }"
            "QSlider::handle:horizontal { width: %dpx; background: #FF8C00;"
            " border-radius: %dpx; margin-top: -%dpx; }"
            % (self._s(4), self._s(2), self._s(8), self._s(4), self._s(2)))
        for button in (self.prev_button, self.play_button, self.next_button):
            button.setStyleSheet(
                "QPushButton { background-color: #FF8C00; color: white;"
                " border: none; border-radius: %dpx; padding: %dpx %dpx; }"
                "QPushButton:pressed { background-color: #e07800; }"
                % (self._s(4), self._s(2), self._s(6)))

    def _apply_size(self):
        self.setFixedSize(self._s(MUSIC_PANEL_WIDTH),
                          self._s(MUSIC_PANEL_HEIGHT))

    def set_scale(self, scale):
        """随桌宠大小一起等比缩放。"""
        scale = max(PET_SCALE_MIN, min(PET_SCALE_MAX, scale))
        if abs(scale - self._scale) < 0.01:
            return
        self._scale = scale
        self._apply_font()
        self._apply_icons()
        self._apply_style()
        self._apply_size()

    def set_title(self, title):
        self.title_label.setText(title)

    def set_playing(self, playing):
        self.play_button.setIcon(self.pause_icon if playing else self.play_icon)

    def set_progress_range(self, duration_ms):
        self.slider.setRange(0, max(0, duration_ms))

    def set_progress(self, position_ms):
        if not self.slider.isSliderDown():
            self.slider.setValue(position_ms)

    def _seek(self):
        self._pet.music_player_seek(self.slider.value())


class EasterEggDialog(QDialog):
    """快速连点 10 次弹出的彩蛋图片：全屏覆盖，7 秒后自动消失，点击或 ESC 也可关闭。"""

    def __init__(self, image_path, parent=None):
        super().__init__(parent)
        self.setWindowTitle("彩蛋")
        self.setWindowFlags(Qt.FramelessWindowHint | Qt.WindowStaysOnTopHint)
        self.setAttribute(Qt.WA_TranslucentBackground)
        pixmap = QPixmap(image_path)
        if pixmap.isNull():
            QMessageBox.warning(self, "提示", "无法打开彩蛋图片：%s" % image_path)
            self.reject()
            return
        # 覆盖整个屏幕（含任务栏）
        screen = QApplication.primaryScreen()
        geometry = screen.geometry() if screen else available_screen_geometry()
        self.setGeometry(geometry)
        # 忽略宽高比，拉伸填满全屏
        scaled = pixmap.scaled(geometry.width(), geometry.height(),
                               Qt.IgnoreAspectRatio, Qt.SmoothTransformation)
        label = QLabel(self)
        label.setPixmap(scaled)
        label.setGeometry(0, 0, geometry.width(), geometry.height())
        # 7 秒后自动关闭
        QTimer.singleShot(RAPID_EGG_DURATION_MS, self.accept)

    def mousePressEvent(self, event):
        self.accept()

    def keyPressEvent(self, event):
        if event.key() == Qt.Key_Escape:
            self.accept()
        else:
            super().keyPressEvent(event)


class MainMenuDialog(QDialog):
    """主菜单弹窗：包含“置顶开关 / 显示/隐藏 / 退出”三个按钮。"""

    def __init__(self, pet, parent=None):
        super().__init__(parent)
        self.pet = pet
        self.setWindowTitle("主菜单")
        self.setModal(True)
        self.setFixedWidth(280)
        self.setFont(QFont("Microsoft YaHei", 10))

        layout = QVBoxLayout(self)
        layout.setSpacing(10)
        layout.setContentsMargins(16, 16, 16, 16)

        self.top_button = QPushButton(self._top_button_text())
        self.top_button.clicked.connect(self._toggle_topmost)
        layout.addWidget(self.top_button)

        # 桌宠大小滑动调节（人物、气泡、文字等比缩放）
        size_row = QHBoxLayout()
        size_label = QLabel("桌宠大小")
        self.size_value_label = QLabel("%d%%" % int(round(pet.pet_scale * 100)))
        self.size_slider = QSlider(Qt.Horizontal)
        self.size_slider.setRange(int(PET_SCALE_MIN * 100), int(PET_SCALE_MAX * 100))
        self.size_slider.setValue(int(round(pet.pet_scale * 100)))
        self.size_slider.valueChanged.connect(self._on_size_changed)
        size_row.addWidget(size_label)
        size_row.addWidget(self.size_slider, 1)
        size_row.addWidget(self.size_value_label)
        layout.addLayout(size_row)

        # 待机状态切换间隔（分钟）
        interval_row = QHBoxLayout()
        interval_label = QLabel("状态切换间隔（分钟）")
        self.interval_spin = QSpinBox()
        self.interval_spin.setRange(1, 1440)
        self.interval_spin.setValue(
            max(1, int(round(pet.idle_interval_ms / 60000))))
        self.interval_spin.valueChanged.connect(self._on_interval_changed)
        interval_row.addWidget(interval_label)
        interval_row.addWidget(self.interval_spin)
        layout.addLayout(interval_row)

        self.autostart_button = QPushButton(self._autostart_text())
        self.autostart_button.clicked.connect(self._toggle_autostart)
        layout.addWidget(self.autostart_button)

        self.meter_button = QPushButton(self._meter_text())
        self.meter_button.clicked.connect(self._toggle_meter)
        layout.addWidget(self.meter_button)

        self.music_path_button = QPushButton(self._music_path_text())
        self.music_path_button.clicked.connect(self._set_music_path)
        layout.addWidget(self.music_path_button)

        self.songs_dir_button = QPushButton(self._songs_dir_text())
        self.songs_dir_button.clicked.connect(self._set_songs_dir)
        layout.addWidget(self.songs_dir_button)

        restart_button = QPushButton("重启桌宠")
        restart_button.clicked.connect(self._restart_pet)
        layout.addWidget(restart_button)

        visible_button = QPushButton("显示/隐藏")
        visible_button.clicked.connect(self._toggle_visible)
        layout.addWidget(visible_button)

        quit_button = QPushButton("退出")
        quit_button.clicked.connect(self._quit)
        layout.addWidget(quit_button)

        self._move_near_pet()

    def _move_near_pet(self):
        """让弹窗显示在桌宠窗口右侧，并限制在屏幕内。"""
        geo = self.pet.frameGeometry()
        screen = available_screen_geometry()
        x = min(geo.right() + 10, screen.right() - self.width() - 4)
        y = max(screen.top() + 4, min(geo.top(), screen.bottom() - self.height() - 4))
        self.move(x, y)

    def _top_button_text(self):
        on = bool(self.pet.windowFlags() & Qt.WindowStaysOnTopHint)
        return "置顶开关（当前：开）" if on else "置顶开关（当前：关）"

    def _toggle_topmost(self):
        """切换置顶状态。"""
        on = not bool(self.pet.windowFlags() & Qt.WindowStaysOnTopHint)
        self.pet.set_topmost(on)
        self.top_button.setText(self._top_button_text())

    def _autostart_text(self):
        return "开机自启（当前：开）" if is_autostart_enabled() else "开机自启（当前：关）"

    def _meter_text(self):
        return "音频电平条（当前：开）" if self.pet.meter_enabled else "音频电平条（当前：关）"

    def _toggle_meter(self):
        """切换音频电平条的显示。"""
        self.pet.set_meter_enabled(not self.pet.meter_enabled)
        self.meter_button.setText(self._meter_text())

    def _music_path_text(self):
        path = self.pet._load_music_config().get("music_path", "")
        return "音乐软件路径：已设置" if path else "音乐软件路径：未设置"

    def _set_music_path(self):
        """选择“我想听歌”启动的音乐软件。"""
        path, _ = QFileDialog.getOpenFileName(
            self, "选择音乐软件", "", "可执行文件 (*.exe)")
        if path:
            if self.pet.set_music_path(path):
                self.music_path_button.setText(self._music_path_text())
            else:
                QMessageBox.warning(self, "提示", "选择的文件无效。")

    def _songs_dir_text(self):
        if self.pet.songs_dir == SONGS_DIR:
            return "歌曲文件夹：默认"
        return "歌曲文件夹：%s" % os.path.basename(self.pet.songs_dir)

    def _set_songs_dir(self):
        """自定义“开始放歌！”的歌曲文件夹。"""
        path = QFileDialog.getExistingDirectory(
            self, "选择歌曲文件夹", self.pet.songs_dir)
        if path:
            if self.pet.set_songs_dir(path):
                self.songs_dir_button.setText(self._songs_dir_text())
            else:
                QMessageBox.warning(self, "提示", "选择的文件夹无效。")

    def _restart_pet(self):
        """重启桌宠。"""
        self.accept()
        self.pet._restart_app()

    def _on_size_changed(self, value):
        """滑动调节桌宠大小。"""
        self.pet.set_pet_scale(value / 100.0)
        self.size_value_label.setText("%d%%" % value)

    def _on_interval_changed(self, minutes):
        """自定义待机状态切换间隔。"""
        self.pet.set_idle_interval(minutes * 60000)

    def _toggle_autostart(self):
        """切换开机自启并更新按钮文字。"""
        enabled = not is_autostart_enabled()
        if set_autostart(enabled):
            self.autostart_button.setText(self._autostart_text())
        else:
            QMessageBox.warning(self, "开机自启", "设置开机自启失败，请检查系统权限。")

    def _toggle_visible(self):
        self.pet.toggle_visible()
        self.accept()

    def _quit(self):
        self.pet.quit_app()


class MusicPathDialog(QDialog):
    """未检测到音乐软件时，让用户手动填写路径或跳过打开网页版。"""

    RESULT_LAUNCH = 1  # 用填写的路径启动
    RESULT_WEB = 2     # 打开网页版网易云

    def __init__(self, parent=None):
        super().__init__(parent)
        self.setWindowTitle("音乐软件")
        self.setModal(True)
        self.setFixedWidth(440)
        self.setFont(QFont("Microsoft YaHei", 10))

        layout = QVBoxLayout(self)
        layout.setSpacing(10)
        layout.setContentsMargins(16, 16, 16, 16)

        tip = QLabel(
            "未检测到网易云 / QQ音乐 / 酷狗 / 酷我音乐，\n"
            "请选择音乐软件路径，或跳过打开网页版网易云。"
        )
        tip.setWordWrap(True)
        layout.addWidget(tip)

        path_row = QHBoxLayout()
        self.path_edit = QLineEdit()
        self.path_edit.setPlaceholderText(
            "例如：C:\\Program Files\\Netease\\CloudMusic\\cloudmusic.exe")
        browse_button = QPushButton("浏览...")
        browse_button.clicked.connect(self._browse)
        path_row.addWidget(self.path_edit, 1)
        path_row.addWidget(browse_button)
        layout.addLayout(path_row)

        button_row = QHBoxLayout()
        launch_button = QPushButton("启动")
        launch_button.clicked.connect(self._on_launch)
        web_button = QPushButton("打开网页版")
        web_button.clicked.connect(self._on_web)
        cancel_button = QPushButton("取消")
        cancel_button.clicked.connect(self.reject)
        button_row.addWidget(launch_button)
        button_row.addWidget(web_button)
        button_row.addWidget(cancel_button)
        layout.addLayout(button_row)

    def path(self):
        """返回用户填写的软件路径。"""
        return self.path_edit.text().strip().strip('"')

    def _browse(self):
        path, _ = QFileDialog.getOpenFileName(
            self, "选择音乐软件", "", "可执行文件 (*.exe)")
        if path:
            self.path_edit.setText(path)

    def _on_launch(self):
        if not os.path.isfile(self.path()):
            QMessageBox.warning(self, "提示", "路径无效，请重新选择或取消。")
            return
        self.done(self.RESULT_LAUNCH)

    def _on_web(self):
        self.done(self.RESULT_WEB)


class DesktopPet(QWidget):
    """桌面宠物主窗口。"""

    def __init__(self):
        super().__init__()
        self._settings_ready = False  # 初始设置应用完成前不写入配置文件
        self.current_state = DEFAULT_STATE
        self.walk_mode = False      # 散步模式是否开启
        self.dragging = False       # 是否正在拖拽
        self.bubble = None          # 对话气泡（懒加载）
        self._sound_player = None   # 音频播放器（懒加载）
        self.pet_scale = 1.0        # 桌宠整体缩放系数（人物+气泡+文字等比）
        self.idle_interval_ms = IDLE_INTERVAL_MS  # 待机状态切换间隔（可自定义）

        self._walk_direction = (0, 0)  # 散步模式当前移动方向（上下左右）
        self._walk_ticks_left = 0      # 当前方向剩余移动步数
        self._state_before_walk = None # 进入散步模式前的状态（退出时恢复）
        self._fixed_walk_state = None  # 散步模式固定的左右移动动作
        self._mirrored = False         # 当前动画是否水平镜像（左右朝向）
        self.audio_level = 0.0         # 最近采集到的系统音量（0~1）
        self._sound_active = False     # 是否因声音处于“看书”状态
        self._silent_ticks = 0         # 连续静音计数
        self._sound_ticks = 0          # 连续外部声音计数（满 3 秒触发看书）
        self._ignore_sound_until = 0.0 # 自己播放的语音忽略到此刻（time.monotonic）
        self._state_before_sound = None  # 切到看书前的状态
        self._audio_running = False    # 音频采集线程开关
        self.meter_enabled = True      # 音频电平条显示开关
        self.song_playlist = []        # 当前歌曲列表（完整路径）
        self.song_index = 0            # 当前歌曲下标
        self._mci_alias = "petmusic"   # MCI 播放器别名
        self._mci_active = False       # MCI 是否正在播放
        self._mci_paused = False       # MCI 是否已暂停
        self._mci_length = 0           # 当前歌曲时长（毫秒）
        self._music_failures = 0       # 连续播放失败计数（播放成功即清零）
        self._failed_songs = set()     # 已计失败的歌曲（同一首歌只计一次）
        self._current_song_path = None # 当前请求播放的歌曲路径
        self._drag_start = QPoint()
        self._drag_offset = QPoint()
        self._drag_moved = False
        self._really_quit = False
        self._tray_notice_shown = False

        self._setup_window()
        self._setup_movie()
        self._setup_timers()
        self._setup_tray()
        self.ui_images = self._load_ui_images()
        self._move_to_bottom_right()
        self.switch_state(DEFAULT_STATE)
        self.meter = AudioLevelMeter(self)  # 左侧五条音频电平条
        self._position_meter()
        self.music_panel = MusicPlayerPanel(self)  # 右侧音乐控制面板
        self.music_panel_visible = False  # 面板默认隐藏，点“开始放歌！”才弹出
        self.music_panel.hide()
        self._position_music_panel()
        self.music_playing = False     # “开始放歌！”开关状态
        self._rapid_clicks = 0         # 快速连点计数
        self._last_click_time = 0.0    # 上次点击时间
        self._easter_dialog = None     # 彩蛋图片窗口引用
        # 歌曲文件夹：优先使用用户自定义的配置，否则用默认文件夹
        saved_songs = self._load_music_config().get("songs_dir", "")
        self.songs_dir = saved_songs if os.path.isdir(saved_songs) else SONGS_DIR
        self._apply_saved_settings()
        self._start_audio_monitor()

    def _load_settings(self):
        """读取保存过的桌宠设置。"""
        try:
            with open(SETTINGS_FILE, "r", encoding="utf-8") as fh:
                data = json.load(fh)
            if isinstance(data, dict):
                return data
        except Exception:
            pass
        return {}

    def _save_settings(self):
        """把桌宠设置写入配置文件（初始应用完成前不写入）。"""
        if not self._settings_ready:
            return
        try:
            data = {
                "pet_scale": self.pet_scale,
                "idle_interval_ms": self.idle_interval_ms,
                "meter_enabled": self.meter_enabled,
                "topmost": bool(self.windowFlags() & Qt.WindowStaysOnTopHint),
            }
            with open(SETTINGS_FILE, "w", encoding="utf-8") as fh:
                json.dump(data, fh, ensure_ascii=False, indent=2)
        except Exception as exc:
            print("[警告] 保存设置失败：", exc)

    def _apply_saved_settings(self):
        """启动时恢复上次保存的设置（桌宠大小/间隔/电平条/置顶）。"""
        settings = self._load_settings()
        # 置顶状态
        if not bool(settings.get("topmost", True)):
            self.setWindowFlag(Qt.WindowStaysOnTopHint, False)
        # 桌宠大小（同步缩放气泡、电平条、音乐面板）
        scale = float(settings.get("pet_scale", 1.0))
        self.set_pet_scale(scale)
        # 状态切换间隔
        interval = int(settings.get("idle_interval_ms", IDLE_INTERVAL_MS))
        self.idle_interval_ms = max(60000, min(24 * 3600 * 1000, interval))
        if not self.walk_mode:
            self.idle_timer.start(self.idle_interval_ms)
        # 音频电平条开关
        enabled = bool(settings.get("meter_enabled", True))
        self.meter_enabled = enabled
        if enabled:
            if self.isVisible():
                self.meter.show()
                self._position_meter()
        else:
            self.meter.hide()
        self._settings_ready = True

    # --------------------------- 初始化 ---------------------------

    def _setup_window(self):
        """设置透明、无边框、置顶、工具栏样式的窗口。"""
        self.setWindowFlags(Qt.FramelessWindowHint
                            | Qt.WindowStaysOnTopHint
                            | Qt.Tool)
        self.setAttribute(Qt.WA_TranslucentBackground)
        self.setFixedSize(WINDOW_SIZE, WINDOW_SIZE)

        self.movie_label = QLabel(self)
        self.movie_label.setAlignment(Qt.AlignCenter)
        self.movie_label.setGeometry(0, 0, WINDOW_SIZE, WINDOW_SIZE)

    def _setup_movie(self):
        """初始化 QMovie，用于播放 GIF（逐帧取图绘制，支持水平镜像）。"""
        self.movie = QMovie(self)
        self.movie.setScaledSize(QSize(WINDOW_SIZE, WINDOW_SIZE))
        self.movie.error.connect(self._on_movie_error)
        self.movie.frameChanged.connect(self._update_frame)
        self.movie_label.setScaledContents(True)

    def _update_frame(self, frame_number=0):
        """把 QMovie 当前帧绘制到标签上；开启镜像时水平翻转。"""
        pixmap = self.movie.currentPixmap()
        if pixmap.isNull():
            return
        if self._mirrored:
            pixmap = pixmap.transformed(
                QTransform().scale(-1, 1), Qt.SmoothTransformation)
        self.movie_label.setPixmap(pixmap)

    def _setup_timers(self):
        """待机定时器、散步定时器、声音检测定时器。"""
        self.idle_timer = QTimer(self)
        self.idle_timer.timeout.connect(self._random_idle_state)
        self.idle_timer.start(IDLE_INTERVAL_MS)

        self.walk_timer = QTimer(self)
        self.walk_timer.timeout.connect(self._walk_step)

        self.audio_timer = QTimer(self)
        self.audio_timer.setInterval(AUDIO_POLL_MS)
        self.audio_timer.timeout.connect(self._on_audio_tick)
        self.audio_timer.start()

        self.mci_timer = QTimer(self)
        self.mci_timer.setInterval(MCI_POLL_MS)
        self.mci_timer.timeout.connect(self._mci_poll)
        self.mci_timer.start()

    def _setup_tray(self):
        """创建系统托盘图标与右键菜单。"""
        self.tray = None
        if not QSystemTrayIcon.isSystemTrayAvailable():
            return
        try:
            self.tray = QSystemTrayIcon(self._make_tray_icon(), self)
            menu = QMenu()

            show_action = menu.addAction("显示/隐藏")
            show_action.triggered.connect(self.toggle_visible)

            quit_action = menu.addAction("退出")
            quit_action.triggered.connect(self.quit_app)

            self.tray.setContextMenu(menu)
            self.tray.activated.connect(self._on_tray_activated)
            self.tray.show()
        except Exception as exc:
            # 托盘不可用时不影响主程序运行
            print("[警告] 系统托盘初始化失败：", exc)
            self.tray = None

    def _load_ui_images(self):
        """加载 ui 文件夹中的气泡装饰图片（1-7.png）。"""
        images = {}
        try:
            for idx in range(1, 8):
                path = os.path.join(UI_DIR, "%d.png" % idx)
                if os.path.isfile(path):
                    pix = QPixmap(path)
                    if not pix.isNull():
                        images[idx] = pix
        except Exception as exc:
            print("[警告] 加载 ui 装饰图片失败：", exc)
        return images

    def _move_to_bottom_right(self):
        """初始位置：屏幕右下角。"""
        screen = available_screen_geometry()
        x = screen.right() - WINDOW_SIZE - SCREEN_MARGIN
        y = screen.bottom() - WINDOW_SIZE - SCREEN_MARGIN
        self.move(x, y)

    def set_pet_scale(self, scale):
        """调整桌宠大小：窗口、GIF、气泡、文字、装饰全部等比缩放。"""
        scale = max(PET_SCALE_MIN, min(PET_SCALE_MAX, scale))
        if abs(scale - self.pet_scale) < 0.01:
            return
        self.pet_scale = scale
        size = max(50, int(round(WINDOW_SIZE * scale)))
        self.setFixedSize(size, size)
        self.movie_label.setGeometry(0, 0, size, size)
        self.movie.setScaledSize(QSize(size, size))
        # 重新加载当前 GIF 以应用新尺寸
        self.switch_state(self.current_state)
        # 气泡同步等比缩放
        if self.bubble is not None:
            self.bubble.set_scale(scale)
        # 电平条同步等比缩放
        self.meter.set_scale(scale)
        # 音乐面板同步等比缩放
        self.music_panel.set_scale(scale)
        # 保持窗口在屏幕内
        self._move_inside_screen(self.pos())
        if self.isVisible():
            self.raise_()
        self._save_settings()

    def set_meter_enabled(self, enabled):
        """开启/关闭左侧音频电平条。"""
        self.meter_enabled = bool(enabled)
        if self.meter_enabled:
            if self.isVisible():
                self.meter.show()
                self._position_meter()
        else:
            self.meter.hide()
        self._save_settings()

    def set_idle_interval(self, interval_ms):
        """自定义待机状态切换间隔（1 分钟 ~ 24 小时），散步模式下暂停、退出后生效。"""
        interval_ms = max(60000, min(24 * 3600 * 1000, interval_ms))
        self.idle_interval_ms = interval_ms
        if not self.walk_mode:
            self.idle_timer.start(interval_ms)  # 立即重启定时器
        self._save_settings()

    def set_topmost(self, on):
        """切换置顶并保存设置。"""
        self.setWindowFlag(Qt.WindowStaysOnTopHint, bool(on))
        self.show()  # 修改窗口标志后需要重新显示
        self.raise_()
        self._save_settings()

    # --------------------------- 状态管理 ---------------------------

    def switch_state(self, state):
        """切换到指定状态并播放对应 GIF；文件缺失时显示占位文字。"""
        if state not in STATE_TO_GIF:
            return
        # 手动选择非移动状态时自动退出散步模式，避免被移动动画覆盖
        if self.walk_mode and state not in WALK_STATES:
            self.set_walk_mode(False)

        self.current_state = state
        gif_path = os.path.join(GIF_DIR, STATE_TO_GIF[state])
        self.movie.stop()
        self.movie_label.setStyleSheet("")
        self.movie_label.setText("")

        if not os.path.isfile(gif_path):
            self._show_placeholder(state, "GIF 文件不存在：%s" % gif_path)
            return

        self.movie.setFileName(gif_path)
        if not self.movie.isValid():
            self._show_placeholder(state, "无法读取 GIF 文件：%s" % gif_path)
            return

        self.movie.start()

    def _show_placeholder(self, state, reason):
        """GIF 缺失或损坏时显示文字占位，保证程序不崩溃。"""
        print("[警告]", reason, "使用文字占位显示")
        self.movie.stop()
        self.movie_label.setText(state)
        self.movie_label.setAlignment(Qt.AlignCenter)
        self.movie_label.setStyleSheet(
            "background-color: #FF8C00; color: white; font-size: 22px;"
            "font-family: Microsoft YaHei; border-radius: 100px;"
        )

    def _on_movie_error(self, error_id):
        """QMovie 播放出错时的兜底处理。"""
        print("[警告] QMovie 播放出错，错误码：", error_id)
        self._show_placeholder(self.current_state, "GIF 播放出错")

    def _random_idle_state(self):
        """待机：随机切换到与当前不同的状态（排除散步模式专用动作）。"""
        candidates = [
            name for name, _ in STATES
            if name not in WALK_STATES and name != self.current_state
        ]
        if candidates:
            self.switch_state(random.choice(candidates))

    # --------------------------- 散步模式 ---------------------------

    def set_walk_mode(self, on):
        """开启/关闭散步模式。"""
        if on == self.walk_mode:
            return
        self.walk_mode = on
        if on:
            # 散步期间暂停待机切换，避免随机状态覆盖移动动作
            self.idle_timer.stop()
            self._state_before_walk = self.current_state  # 记住散步前状态
            # 进入散步模式时固定一个左右移动动作，整个散步过程不再随机切换
            self._fixed_walk_state = random.choice(WALK_HORIZONTAL_STATES)
            self._pick_new_direction()  # 选方向并应用对应动画（含镜像 / 潜水）
            self.walk_timer.start(WALK_INTERVAL_MS)
        else:
            self.walk_timer.stop()
            self.idle_timer.start(self.idle_interval_ms)
            self._restore_state_after_walk()
            if self._sound_active:
                # 散步时检测到的声音仍在：退出散步后切回看书状态
                self._apply_sound_state()

    def _walk_step(self):
        """沿当前方向移动；方向持续几十秒后换向，碰屏幕边缘时反弹。"""
        # 当前方向持续时间已到，重新随机选择一个方向
        if self._walk_ticks_left <= 0:
            self._pick_new_direction()  # 内部会按新方向应用动画

        step = random.randint(WALK_MIN_STEP, WALK_MAX_STEP)
        dx, dy = self._walk_direction
        dx *= step
        dy *= step
        new_pos = self.pos() + QPoint(dx, dy)

        _, hit_x, hit_y = self._move_inside_screen(new_pos)
        if hit_x:
            # 碰到左右边界：水平分量反弹
            self._walk_direction = (-self._walk_direction[0], self._walk_direction[1])
        if hit_y:
            # 碰到上下边界：垂直分量反弹
            self._walk_direction = (self._walk_direction[0], -self._walk_direction[1])
        if hit_x or hit_y:
            # 反弹后方向可能改变，按新方向重新应用动画
            self._apply_walk_animation()

        self._walk_ticks_left -= 1

    def _pick_new_direction(self):
        """等概率随机选择上下左右方向，并设定该方向的持续步数。"""
        self._walk_direction = random.choice(
            [(-1, 0), (1, 0), (0, -1), (0, 1)])

        duration = random.randint(WALK_DIRECTION_MIN_MS, WALK_DIRECTION_MAX_MS)
        self._walk_ticks_left = max(1, duration // WALK_INTERVAL_MS)
        self._apply_walk_animation()

    def _apply_walk_animation(self):
        """散步中按方向应用动画：
        上下移动用潜水；左右移动用固定动作并按朝向水平镜像
        （骑行向右正常、向左镜像；送货/纸飞机向左正常、向右镜像）。
        """
        dx, dy = self._walk_direction
        if dy != 0:
            # 上 / 下：使用潜水，不镜像
            self._mirrored = False
            if self.current_state != "潜水":
                self.switch_state("潜水")
            self._update_frame()
            return

        # 左 / 右：使用散步固定动作
        if self._fixed_walk_state == "骑行":
            self._mirrored = dx < 0  # 骑行：向右正常，向左镜像
        else:
            self._mirrored = dx > 0  # 送货/纸飞机：向左正常，向右镜像
        if self.current_state != self._fixed_walk_state:
            self.switch_state(self._fixed_walk_state)
        self._update_frame()

    def _restore_state_after_walk(self):
        """取消散步模式后切回散步前的状态；无效时随机选一个非移动状态。"""
        self._mirrored = False  # 恢复正常朝向
        previous = self._state_before_walk
        if previous is not None and previous in STATE_TO_GIF and previous not in WALK_STATES:
            self.switch_state(previous)
        else:
            candidates = [name for name, _ in STATES if name not in WALK_STATES]
            if candidates:
                self.switch_state(random.choice(candidates))
        self._state_before_walk = None

    # --------------------------- 音频电平 ---------------------------

    def _log_audio(self, msg):
        """把音频采集过程写入调试日志（exe 无控制台，用文件定位问题）。"""
        try:
            with open(AUDIO_DEBUG_LOG, "a", encoding="utf-8") as fh:
                fh.write(time.strftime("%Y-%m-%d %H:%M:%S") + " " + msg + "\n")
        except Exception:
            pass

    def _start_audio_monitor(self):
        """后台线程采集系统声音音量（soundcard 回环采集）。"""
        self._audio_running = True
        threading.Thread(target=self._audio_loop, daemon=True).start()

    def _audio_loop(self):
        """循环采集系统回环音频，计算音量并写入 audio_level（0~1）。

        注意：soundcard 的回环采集要使用“回环麦克风”（Loopback），
        而不是扬声器对象的 recorder（扬声器没有该方法）。
        soundcard 的 Windows 后端基于 COM，且 COM 初始化只在导入它的线程
        生效，因此必须让 soundcard 在本采集线程内导入（不能在主线程提前导入），
        否则 CoCreateInstance 会报 0x800401F0（COM 未初始化）。
        """
        try:
            # 在本线程导入 soundcard（其模块初始化会同时初始化 COM）
            try:
                import soundcard as sc
            except ImportError:
                self._log_audio("未安装 soundcard，音频电平功能不可用。")
                return
            import numpy as np
            self._log_audio("soundcard 导入成功")
            speaker = sc.default_speaker()
            self._log_audio("默认扬声器: %r" % (speaker,))
            if speaker is None:
                self._log_audio("无默认扬声器，停止采集")
                return
            # 找与默认扬声器同名的回环麦克风
            mic = sc.get_microphone(id=str(speaker.name), include_loopback=True)
            self._log_audio("回环麦克风: %r" % (mic,))
            if mic is None:
                # 兜底：任选第一个可用的回环麦克风
                mics = [m for m in sc.all_microphones(include_loopback=True)
                        if getattr(m, "isloopback", False)]
                self._log_audio("兜底回环麦克风列表: %r" % (mics,))
                mic = mics[0] if mics else None
            if mic is None:
                self._log_audio("没有可用回环麦克风，停止采集")
                return
            with mic.recorder(samplerate=AUDIO_SAMPLE_RATE, channels=1,
                              blocksize=AUDIO_BLOCKSIZE) as recorder:
                self._log_audio("回环采集已打开")
                count = 0
                while self._audio_running:
                    data = recorder.record(numframes=AUDIO_BLOCKSIZE)
                    rms = float(np.sqrt(np.mean(np.square(data))))
                    self.audio_level = min(1.0, rms * AUDIO_RMS_GAIN)
                    count += 1
                    if count % 1800 == 0:
                        self._log_audio("level=%.3f" % self.audio_level)
        except Exception as exc:
            self._log_audio("采集异常: %r\n%s" % (exc, traceback.format_exc()))
            self.audio_level = 0.0

    def _on_audio_tick(self):
        """声音检测：自己播放的语音不触发；外部声音持续 3 秒切看书，静音后恢复。"""
        has_sound = self.audio_level > METER_SOUND_THRESHOLD
        # 自己播放的语音（点击气泡的语音包）不算外部声音
        external_sound = has_sound and time.monotonic() >= self._ignore_sound_until
        if external_sound:
            self._silent_ticks = 0
            self._sound_ticks += 1
            if (not self._sound_active
                    and self._sound_ticks * AUDIO_POLL_MS >= METER_SOUND_TRIGGER_MS):
                self._sound_active = True
                self._apply_sound_state()
        else:
            self._silent_ticks += 1
            self._sound_ticks = 0
            if (self._sound_active
                    and self._silent_ticks * AUDIO_POLL_MS
                    >= METER_SILENT_RESTORE_MS):
                self._sound_active = False
                self._restore_state_after_sound()

    def _apply_sound_state(self):
        """检测到声音：非散步模式时切到看书状态，并暂停待机切换。"""
        if self.walk_mode:
            return  # 散步中不打断移动动作
        if self.current_state != "看书":
            self._state_before_sound = self.current_state
            self.switch_state("看书")
        self.idle_timer.stop()

    def _restore_state_after_sound(self):
        """声音停止后恢复原状态，并重启待机切换。"""
        state = self._state_before_sound
        self._state_before_sound = None
        if state and state in STATE_TO_GIF:
            self.switch_state(state)
        if not self.walk_mode:
            self.idle_timer.start(self.idle_interval_ms)

    def _position_meter(self):
        """把电平条放到桌宠左侧垂直居中。"""
        if self.meter is None:
            return
        x = self.x() - self.meter.width() - 8
        y = self.y() + (self.height() - self.meter.height()) // 2
        screen = available_screen_geometry()
        x = max(screen.left() + 4, x)
        y = max(screen.top() + 4,
                min(y, screen.bottom() - self.meter.height() - 4))
        self.meter.move(x, y)

    def _move_inside_screen(self, pos):
        """移动窗口并做边界检测；返回 (实际位置, 是否碰左右边界, 是否碰上下边界)。"""
        screen = available_screen_geometry()
        max_x = screen.right() - self.width() + 1
        max_y = screen.bottom() - self.height() + 1
        x = max(screen.left(), min(pos.x(), max_x))
        y = max(screen.top(), min(pos.y(), max_y))
        self.move(x, y)
        return QPoint(x, y), x != pos.x(), y != pos.y()

    # --------------------------- 鼠标交互 ---------------------------

    def mousePressEvent(self, event):
        """记录拖拽起点与偏移量，并统计快速连点（按下时刻计时）。"""
        if event.button() == Qt.LeftButton:
            self.dragging = True
            self._drag_moved = False
            self._drag_start = event.globalPos()
            self._drag_offset = event.globalPos() - self.frameGeometry().topLeft()
            self._track_rapid_click()  # 按下即计数，避免按住时长影响连点判定
            self._sync_walk_timer()  # 拖拽期间暂停散步
            event.accept()
        else:
            super().mousePressEvent(event)

    def mouseMoveEvent(self, event):
        """左键按下时拖动窗口。"""
        if self.dragging and event.buttons() & Qt.LeftButton:
            if not self._drag_moved:
                self._drag_moved = (event.globalPos() - self._drag_start).manhattanLength() > 4
            if self._drag_moved:
                self._move_inside_screen(event.globalPos() - self._drag_offset)
            event.accept()
        else:
            super().mouseMoveEvent(event)

    def mouseReleaseEvent(self, event):
        """左键释放：未发生拖拽则视为单击，弹出对话气泡。"""
        if event.button() == Qt.LeftButton and self.dragging:
            self.dragging = False
            if not self._drag_moved:
                self.show_bubble()
            self._sync_walk_timer()
            event.accept()
        else:
            super().mouseReleaseEvent(event)

    def _track_rapid_click(self):
        """统计快速连点（间隔 < 0.3 秒），满 10 次弹出彩蛋图片。"""
        now = time.monotonic()
        if now - self._last_click_time < RAPID_CLICK_INTERVAL:
            self._rapid_clicks += 1
        else:
            self._rapid_clicks = 1
        self._last_click_time = now
        if self._rapid_clicks >= RAPID_CLICK_COUNT:
            self._rapid_clicks = 0
            self._show_easter_egg()

    def _find_easter_image(self):
        """在程序目录及子目录查找彩蛋 jpg 图片。"""
        try:
            for name in os.listdir(BASE_DIR):
                if name.lower().endswith(".jpg"):
                    return os.path.join(BASE_DIR, name)
            for root, _, files in os.walk(BASE_DIR):
                for name in files:
                    if name.lower().endswith(".jpg"):
                        return os.path.join(root, name)
        except Exception:
            return None
        return None

    def _show_easter_egg(self):
        """快速连点 10 次后弹出彩蛋图片。"""
        image = self._find_easter_image()
        if image is None:
            return
        if self._easter_dialog is not None:
            self._easter_dialog.close()
        self._easter_dialog = EasterEggDialog(image)
        self._easter_dialog.show()
        self._easter_dialog.raise_()
        self._easter_dialog.activateWindow()

    def contextMenuEvent(self, event):
        """右键弹出菜单：主菜单 / 状态选择 / 散步模式。"""
        menu = QMenu(self)

        main_action = menu.addAction("主菜单")
        main_action.triggered.connect(self.show_main_menu)

        music_action = menu.addAction("我想听歌")
        music_action.triggered.connect(self.start_music)

        song_action = menu.addAction("开始放歌！")
        song_action.setCheckable(True)
        song_action.setChecked(self.music_playing)
        # triggered 只在用户点击时触发（setChecked 不会触发），避免打开菜单误启动
        song_action.triggered.connect(self.toggle_music_feature)

        meter_action = menu.addAction("音频电平条")
        meter_action.setCheckable(True)
        meter_action.setChecked(self.meter_enabled)
        meter_action.toggled.connect(self.set_meter_enabled)

        state_menu = menu.addMenu("状态选择")
        for state, _ in STATES:
            action = state_menu.addAction(state)
            action.setCheckable(True)
            action.setChecked(state == self.current_state)
            action.triggered.connect(lambda checked=False, s=state: self.switch_state(s))

        walk_action = menu.addAction("散步模式")
        walk_action.setCheckable(True)
        walk_action.setChecked(self.walk_mode)
        walk_action.toggled.connect(self.set_walk_mode)

        menu.exec_(event.globalPos())

    # --------------------------- 气泡 ---------------------------

    def show_bubble(self):
        """显示对话气泡：优先使用“语音包和文字”中配对的文字与语音，否则回退到 texts/audio。"""
        pairs = self._load_voice_pairs()
        if pairs:
            # 语音包：文字和对应的 wav 一起使用
            text, wav_path = random.choice(pairs)
        else:
            # 回退：texts 文件夹随机文字 + audio 文件夹随机声音
            text = self._get_bubble_text()
            wav_path = None
        if self.bubble is None:
            self.bubble = BubbleWidget(text, self, ui_images=self.ui_images,
                                       scale=self.pet_scale)
        else:
            self.bubble.set_text(text)
        self.bubble.show_above(self.frameGeometry())
        self._play_sound(wav_path)

    def moveEvent(self, event):
        """桌宠窗口移动（拖拽/散步）时，让气泡、电平条、音乐面板跟随。"""
        super().moveEvent(event)
        if self.bubble is not None and self.bubble.isVisible():
            self.bubble.start_follow()
        if self.meter is not None:
            self._position_meter()
        if self.music_panel is not None:
            self._position_music_panel()

    def showEvent(self, event):
        """桌宠显示时同步显示电平条和音乐面板。"""
        super().showEvent(event)
        if self.meter is not None and self.meter_enabled:
            self.meter.show()
            self._position_meter()
        if self.music_panel is not None and self.music_panel_visible:
            self.music_panel.show()
            self._position_music_panel()

    def hideEvent(self, event):
        """桌宠隐藏时同步隐藏电平条和音乐面板。"""
        if self.meter is not None:
            self.meter.hide()
        if self.music_panel is not None:
            self.music_panel.hide()
        super().hideEvent(event)

    def _load_bubble_texts(self):
        """读取 texts 文件夹中所有 .txt 文件内容作为候选对话文字。"""
        texts = []
        try:
            files = [f for f in os.listdir(TEXT_DIR) if f.lower().endswith(".txt")]
        except OSError:
            return texts
        for name in files:
            content = self._read_text_file(os.path.join(TEXT_DIR, name))
            if content:
                texts.append(content)
        return texts

    def _get_bubble_text(self):
        """随机取一句对话；texts 文件夹为空时使用默认文字。"""
        texts = self._load_bubble_texts()
        return random.choice(texts) if texts else BUBBLE_TEXT

    def _read_text_file(self, path):
        """读取文本文件，兼容 UTF-8 / UTF-8 BOM / GBK 编码；返回去首尾空白内容或 None。"""
        try:
            with open(path, "rb") as fh:
                raw = fh.read()
            try:
                content = raw.decode("utf-8-sig").strip()
            except UnicodeDecodeError:
                # 兼容 GBK 编码的文本文件
                content = raw.decode("gbk").strip()
            return content or None
        except (OSError, UnicodeDecodeError):
            return None

    def _load_voice_pairs(self):
        """扫描“语音包和文字”文件夹，按同名文件配对 txt 与 wav，返回 [(文字, wav路径)]。"""
        pairs = []
        try:
            entries = os.listdir(VOICE_DIR)
        except OSError:
            return pairs

        # 按文件名主干（不含扩展名）分组
        by_stem = {}
        for name in entries:
            full = os.path.join(VOICE_DIR, name)
            if not os.path.isfile(full):
                continue
            stem, ext = os.path.splitext(name)
            ext = ext.lower()
            if ext in (".txt", ".wav"):
                by_stem.setdefault(stem, {})[ext] = full

        # 只有同名 txt 和 wav 都存在时才构成一组语音包
        for files in by_stem.values():
            if ".txt" in files and ".wav" in files:
                text = self._read_text_file(files[".txt"])
                if text:
                    pairs.append((text, files[".wav"]))
        return pairs

    # --------------------------- 音频播放 ---------------------------

    def _init_sound_player(self):
        """初始化 QMediaPlayer（支持 mp3/wav 等格式）。"""
        try:
            from PyQt5.QtMultimedia import QMediaContent, QMediaPlayer
            self._sound_player = QMediaPlayer(self)
        except Exception as exc:
            print("[警告] 音频播放初始化失败：", exc)
            self._sound_player = None

    def _media_duration_ms(self, path):
        """解析音频时长（毫秒），无法解析时返回 None。"""
        try:
            import wave
            with wave.open(path, "rb") as wf:
                rate = wf.getframerate()
                if rate <= 0:
                    return None
                return int(wf.getnframes() * 1000 / rate)
        except Exception:
            return None

    def _play_sound(self, path=None):
        """播放指定音频；path 为空时从 audio 文件夹随机选一个，均无则静音。"""
        try:
            if path is None:
                if not os.path.isdir(AUDIO_DIR):
                    return
                files = [f for f in os.listdir(AUDIO_DIR)
                         if os.path.splitext(f)[1].lower() in AUDIO_EXTS]
                if not files:
                    return
                path = os.path.join(AUDIO_DIR, random.choice(files))

            if not os.path.isfile(path):
                return

            # 气泡显示时长与音频播放时长保持一致
            duration = self._media_duration_ms(path)
            if duration and self.bubble is not None:
                self.bubble.set_duration(duration)
            # 自己播放的语音不触发状态切换：播放期间（含 0.5 秒余量）忽略声音检测
            self._ignore_sound_until = (
                time.monotonic() + (duration or 3000) / 1000.0 + 0.5)

            if self._sound_player is None:
                self._init_sound_player()

            if self._sound_player is not None:
                from PyQt5.QtMultimedia import QMediaContent
                self._sound_player.stop()
                self._sound_player.setMedia(QMediaContent(QUrl.fromLocalFile(path)))
                self._sound_player.play()
            elif path.lower().endswith(".wav"):
                # 兜底：QtMultimedia 不可用时用系统 winsound 播放 wav
                import winsound
                winsound.PlaySound(path, winsound.SND_FILENAME | winsound.SND_ASYNC)
        except Exception as exc:
            print("[警告] 播放音频失败：", exc)

    # --------------------------- 主菜单 / 托盘 ---------------------------

    def show_main_menu(self):
        """弹出主菜单对话框。"""
        MainMenuDialog(self, self).exec_()

    def toggle_visible(self):
        """显示/隐藏桌宠。"""
        if self.isVisible():
            self.hide()
            if self.bubble is not None:
                self.bubble.hide()
        else:
            self.show()
            self.raise_()
        self._sync_walk_timer()

    def _on_tray_activated(self, reason):
        """单击/双击托盘图标时显示桌宠。"""
        if reason in (QSystemTrayIcon.Trigger, QSystemTrayIcon.DoubleClick):
            if not self.isVisible():
                self.toggle_visible()

    def _sync_walk_timer(self):
        """根据当前状态决定散步定时器是否运行。"""
        should_run = self.walk_mode and self.isVisible() and not self.dragging
        if should_run and not self.walk_timer.isActive():
            self.walk_timer.start(WALK_INTERVAL_MS)
        elif not should_run and self.walk_timer.isActive():
            self.walk_timer.stop()

    # --------------------------- 开始放歌 ---------------------------

    def _load_music_config(self):
        """读取保存过的音乐软件路径 / 歌曲文件夹配置。"""
        try:
            with open(MUSIC_CONFIG_FILE, "r", encoding="utf-8") as fh:
                data = json.load(fh)
            if isinstance(data, dict):
                return data
        except Exception:
            pass
        return {}

    def _save_music_config(self, music_path=None, songs_dir=None):
        """保存音乐软件路径 / 歌曲文件夹配置，下次直接使用。"""
        try:
            data = self._load_music_config()
            if music_path is not None:
                data["music_path"] = music_path
            if songs_dir is not None:
                data["songs_dir"] = songs_dir
            with open(MUSIC_CONFIG_FILE, "w", encoding="utf-8") as fh:
                json.dump(data, fh, ensure_ascii=False, indent=2)
        except Exception as exc:
            print("[警告] 保存音乐软件配置失败：", exc)

    def set_music_path(self, path):
        """设置“我想听歌”使用的音乐软件路径。"""
        if path and os.path.isfile(path):
            self._save_music_config(music_path=path)
            return True
        return False

    def set_songs_dir(self, path):
        """自定义“开始放歌！”的歌曲文件夹。"""
        if path and os.path.isdir(path):
            self.songs_dir = path
            self._save_music_config(songs_dir=path)
            return True
        return False

    def _find_music_app(self):
        """在常见安装位置与注册表中查找音乐软件（网易云/QQ音乐/酷狗/酷我）。"""
        # 常见固定安装路径
        fixed_paths = [
            (r"C:\Program Files\Netease\CloudMusic\cloudmusic.exe", "网易云音乐"),
            (r"C:\Program Files (x86)\Netease\CloudMusic\cloudmusic.exe", "网易云音乐"),
            (r"C:\Program Files\Tencent\QQMusic\QQMusic.exe", "QQ音乐"),
            (r"C:\Program Files (x86)\Tencent\QQMusic\QQMusic.exe", "QQ音乐"),
            (r"C:\Program Files\KuGou\KGMusic\KuGou.exe", "酷狗音乐"),
            (r"C:\Program Files (x86)\KuGou\KGMusic\KuGou.exe", "酷狗音乐"),
            (r"C:\Program Files\Kuwo\KwMusic\kwmusic.exe", "酷我音乐"),
            (r"C:\Program Files (x86)\Kuwo\KwMusic\kwmusic.exe", "酷我音乐"),
        ]
        local_appdata = os.environ.get("LOCALAPPDATA", "")
        if local_appdata:
            fixed_paths.append(
                (os.path.join(local_appdata, "Netease", "CloudMusic",
                              "cloudmusic.exe"), "网易云音乐"))
        for path, _ in fixed_paths:
            if os.path.isfile(path):
                return path

        # 注册表 App Paths（软件自注册的启动路径）
        app_paths = [
            r"SOFTWARE\Microsoft\Windows\CurrentVersion\App Paths\cloudmusic.exe",
            r"SOFTWARE\Microsoft\Windows\CurrentVersion\App Paths\QQMusic.exe",
            r"SOFTWARE\Microsoft\Windows\CurrentVersion\App Paths\KuGou.exe",
            r"SOFTWARE\Microsoft\Windows\CurrentVersion\App Paths\kwmusic.exe",
        ]
        for subkey in app_paths:
            try:
                key = winreg.OpenKey(winreg.HKEY_LOCAL_MACHINE, subkey, 0,
                                     winreg.KEY_READ)
                try:
                    value, _ = winreg.QueryValueEx(key, None)
                    if value and os.path.isfile(value):
                        return value
                finally:
                    key.Close()
            except OSError:
                continue

        # 注册表卸载项：按软件名匹配安装位置
        uninstall_root = (r"SOFTWARE\Microsoft\Windows\CurrentVersion"
                          r"\Uninstall")
        exe_map = [("网易云", "cloudmusic.exe"), ("QQ音乐", "QQMusic.exe"),
                   ("酷狗", "KuGou.exe"), ("酷我", "kwmusic.exe")]
        for hive in (winreg.HKEY_LOCAL_MACHINE, winreg.HKEY_CURRENT_USER):
            try:
                root_key = winreg.OpenKey(hive, uninstall_root, 0, winreg.KEY_READ)
            except OSError:
                continue
            try:
                index = 0
                while True:
                    try:
                        sub_name = winreg.EnumKey(root_key, index)
                        index += 1
                    except OSError:
                        break
                    try:
                        sub_key = winreg.OpenKey(hive, uninstall_root + "\\" + sub_name,
                                                 0, winreg.KEY_READ)
                    except OSError:
                        continue
                    try:
                        display_name = None
                        install_location = None
                        try:
                            display_name, _ = winreg.QueryValueEx(sub_key, "DisplayName")
                        except OSError:
                            pass
                        try:
                            install_location, _ = winreg.QueryValueEx(sub_key, "InstallLocation")
                        except OSError:
                            pass
                    finally:
                        sub_key.Close()
                    if not display_name or not install_location:
                        continue
                    for token, exe_name in exe_map:
                        if token in display_name:
                            full = os.path.join(install_location, exe_name)
                            if os.path.isfile(full):
                                return full
            finally:
                root_key.Close()
        return None

    def _launch_music(self, path):
        """启动音乐软件。"""
        try:
            os.startfile(path)
        except Exception as exc:
            print("[警告] 启动音乐软件失败：", exc)
            QMessageBox.warning(self, "开始放歌", "启动音乐软件失败：%s" % exc)

    def start_music(self):
        """开始放歌：优先启动本地音乐软件；找不到则弹窗填路径；跳过则打开网页版网易云。"""
        # 1. 使用之前保存过的路径
        saved_path = self._load_music_config().get("music_path", "")
        if saved_path and os.path.isfile(saved_path):
            self._launch_music(saved_path)
            return
        # 2. 自动扫描常见安装位置
        found = self._find_music_app()
        if found:
            self._launch_music(found)
            return
        # 3. 弹窗让用户填写路径或跳过
        dialog = MusicPathDialog(self)
        result = dialog.exec_()
        if result == MusicPathDialog.RESULT_LAUNCH:
            self._save_music_config(music_path=dialog.path())
            self._launch_music(dialog.path())
        elif result == MusicPathDialog.RESULT_WEB:
            # 打开网页版网易云“我喜欢的音乐”（需要已登录网页版）
            webbrowser.open("https://music.163.com/#/my/m/music")

    def play_random_song(self):
        """开始放歌！：刷新歌曲列表并随机播放一首（不弹歌名气泡），同时弹出音乐面板。"""
        self.song_playlist = [
            os.path.join(self.songs_dir, name)
            for name in self._load_song_files()
        ]
        if not self.song_playlist:
            QMessageBox.information(
                self, "开始放歌！",
                "歌曲文件夹（%s）中没有音乐，\n请放入 mp3/wav 文件。"
                % os.path.basename(self.songs_dir))
            return
        self.song_index = random.randrange(len(self.song_playlist))
        self._music_failures = 0
        self._failed_songs.clear()
        self.music_playing = True  # 开关状态置为“开”
        # 弹出右侧音乐控制面板
        self.music_panel_visible = True
        if self.isVisible():
            self.music_panel.show()
            self._position_music_panel()
        self._play_song(self.song_playlist[self.song_index])

    def toggle_music_feature(self, enabled):
        """“开始放歌！”开关：勾选=启动播放，取消勾选=停止并隐藏面板。"""
        try:
            if enabled:
                if not self.music_playing:
                    self.play_random_song()
            else:
                self._stop_music()
        except Exception as exc:
            print("[警告] 开始放歌开关异常：", exc)

    def _stop_music(self):
        """停止播放并隐藏音乐面板（关闭“开始放歌！”功能）。"""
        self.music_playing = False
        self._mci_active = False
        self._mci_paused = False
        self._current_song_path = None
        self._music_failures = 0
        self._failed_songs.clear()
        self._mci_command("stop %s" % self._mci_alias)
        self._mci_command("close %s" % self._mci_alias)
        self.music_panel_visible = False
        if self.music_panel is not None:
            self.music_panel.hide()
            self.music_panel.set_playing(False)
            self.music_panel.set_progress_range(0)
            self.music_panel.set_progress(0)

    def _load_song_files(self):
        """列出歌曲文件夹中的音频文件（按文件名排序，方便上一首/下一首）。"""
        try:
            files = [f for f in os.listdir(self.songs_dir)
                     if os.path.splitext(f)[1].lower() in AUDIO_EXTS]
        except OSError:
            files = []
        return sorted(files)

    def _play_song(self, path):
        """播放指定歌曲（Windows MCI 引擎，不依赖 Qt 多媒体）；打不开自动随机换歌。"""
        try:
            title = os.path.splitext(os.path.basename(path))[0]
            if self.music_panel is not None:
                self.music_panel.set_title(title)
            # 弹出歌名气泡
            if self.bubble is None:
                self.bubble = BubbleWidget(title, self, ui_images=self.ui_images,
                                           scale=self.pet_scale)
            else:
                self.bubble.set_text(title)
            self.bubble.show_above(self.frameGeometry())
            self._current_song_path = path
            if not self._mci_open(path):
                # 打不开（文件损坏 / 格式不支持）-> 记一次失败并随机换歌
                self._handle_music_failure(path)
                return
            self._mci_command("play %s" % self._mci_alias)
            self._mci_paused = False
            self._mci_active = True
            self._music_failures = 0
            self._failed_songs.clear()
            # 获取歌曲时长（用于进度条与“播完自动下一首”判断）
            ok, length = self._mci_command("status %s length" % self._mci_alias)
            self._mci_length = int(length) if ok and length.isdigit() else 0
            if self.music_panel is not None:
                self.music_panel.set_progress_range(self._mci_length)
                self.music_panel.set_playing(True)
        except Exception as exc:
            print("[警告] 播放歌曲失败：", exc)

    def _mci_command(self, command):
        """发送 Windows MCI 命令；返回 (是否成功, 返回文本)。"""
        try:
            import ctypes
            buffer = ctypes.create_unicode_buffer(512)
            result = ctypes.windll.winmm.mciSendStringW(command, buffer, 512, None)
            if result != 0:
                error_buffer = ctypes.create_unicode_buffer(256)
                ctypes.windll.winmm.mciGetErrorStringW(result, error_buffer, 256)
                return False, error_buffer.value
            return True, buffer.value
        except Exception as exc:
            print("[警告] MCI 命令失败：", command, exc)
            return False, ""

    def _mci_open(self, path):
        """关闭旧媒体并打开新歌；wav 用 waveaudio（最稳），mp3 用 mpegvideo。"""
        self._mci_command("close %s" % self._mci_alias)
        if path.lower().endswith(".wav"):
            ok, _ = self._mci_command(
                'open "%s" type waveaudio alias %s' % (path, self._mci_alias))
        else:
            ok, _ = self._mci_command(
                'open "%s" type mpegvideo alias %s' % (path, self._mci_alias))
            if not ok:
                # 个别系统没有 mpegvideo 设备时，改用自动探测打开
                ok, _ = self._mci_command(
                    'open "%s" alias %s' % (path, self._mci_alias))
        return ok

    def _mci_poll(self):
        """定时轮询：更新进度条/播放状态，播完或异常停止时自动随机下一首。"""
        if not self._mci_active:
            return
        ok, mode = self._mci_command("status %s mode" % self._mci_alias)
        if not ok:
            return
        _, pos = self._mci_command("status %s position" % self._mci_alias)
        pos_val = int(pos) if pos.isdigit() else 0
        if mode == "playing":
            self._mci_paused = False
            self.music_playing = True
            if self.music_panel is not None:
                self.music_panel.set_playing(True)
        elif mode == "paused":
            self._mci_paused = True
            if self.music_panel is not None:
                self.music_panel.set_playing(False)
        elif mode == "stopped":
            # 正常播完：位置接近时长；否则视为异常停止（解码失败）
            if self._mci_length > 0 and pos_val >= self._mci_length - 500:
                self.play_next()
            else:
                self._handle_music_failure(self._current_song_path)
            return
        if self.music_panel is not None:
            self.music_panel.set_progress(pos_val)

    def play_previous(self):
        """上一首（随机选一首，避免顺序循环）。"""
        try:
            if not self.song_playlist:
                self.play_random_song()
                return
            self.song_index = self._random_song_index()
            self._play_song(self.song_playlist[self.song_index])
        except Exception as exc:
            print("[警告] 上一首失败：", exc)

    def play_next(self):
        """下一首（随机选一首，避免顺序循环）。"""
        try:
            if not self.song_playlist:
                self.play_random_song()
                return
            self.song_index = self._random_song_index()
            self._play_song(self.song_playlist[self.song_index])
        except Exception as exc:
            print("[警告] 下一首失败：", exc)

    def _random_song_index(self):
        """随机选一个与当前不同的歌曲下标。"""
        if len(self.song_playlist) <= 1:
            return self.song_index
        index = self.song_index
        while index == self.song_index:
            index = random.randrange(len(self.song_playlist))
        return index

    def toggle_play_pause(self):
        """播放 / 暂停切换。"""
        try:
            if not self.song_playlist:
                self.play_random_song()
                return
            if not self._mci_active:
                self.play_random_song()
                return
            if self._mci_paused:
                self._mci_command("play %s" % self._mci_alias)
                self._mci_paused = False
            else:
                self._mci_command("pause %s" % self._mci_alias)
                self._mci_paused = True
            if self.music_panel is not None:
                self.music_panel.set_playing(not self._mci_paused)
        except Exception as exc:
            print("[警告] 播放/暂停失败：", exc)

    def music_player_seek(self, position_ms):
        """进度条拖动跳转。"""
        if not self._mci_active:
            return
        self._mci_command("seek %s to %d" % (self._mci_alias, position_ms))
        if not self._mci_paused:
            self._mci_command("play %s" % self._mci_alias)

    def _handle_music_failure(self, path):
        """播放失败自动随机换歌；同一首歌的多个错误只计一次，连续失败过多才停止。"""
        try:
            # 同一首歌的多个错误信号（error / InvalidMedia）只计一次
            if path is None or path in self._failed_songs:
                return
            self._failed_songs.add(path)
            self._music_failures += 1
            limit = max(3, min(6, len(self.song_playlist) or 1))
            if self._music_failures >= limit:
                self._music_failures = 0
                self._stop_music()
                return
            self.play_next()
        except Exception as exc:
            print("[警告] 跳歌失败：", exc)

    def _position_music_panel(self):
        """把音乐控制面板放到桌宠右侧垂直居中。"""
        if self.music_panel is None:
            return
        screen = available_screen_geometry()
        panel_width = self.music_panel.width()
        panel_height = self.music_panel.height()
        y = self.y() + (self.height() - self.music_panel.height()) // 2
        y = max(screen.top() + 4,
                min(y, screen.bottom() - panel_height - 4))
        right_x = self.x() + self.width() + 8
        if right_x + panel_width <= screen.right() - 4:
            # 右侧放得下：放在桌宠右边
            self.music_panel.move(right_x, y)
            return
        # 右侧放不下：放到桌宠左侧（电平条再往左，避免重叠）
        left_x = self.x() - panel_width - 8
        if self.meter is not None and self.meter.isVisible():
            left_x = min(left_x, self.meter.x() - panel_width - 4)
        left_x = max(screen.left() + 4, left_x)
        self.music_panel.move(left_x, y)

    def quit_app(self):
        """真正退出程序。"""
        self._really_quit = True
        self._save_settings()  # 退出前保存当前设置
        self._audio_running = False  # 停止音频采集线程
        if self.tray is not None:
            self.tray.hide()
        QApplication.instance().quit()

    def _restart_app(self):
        """重启桌宠：先启动新实例，稍后关闭当前实例（设置会自动恢复）。"""
        try:
            if getattr(sys, "frozen", False):
                command = [sys.executable]
            else:
                command = [sys.executable, os.path.abspath(__file__)]
            subprocess.Popen(command, cwd=BASE_DIR)
        except Exception as exc:
            print("[警告] 重启失败：", exc)
            QMessageBox.warning(self, "重启桌宠", "启动新实例失败：%s" % exc)
            return
        # 给新实例一点启动时间，再退出当前实例（退出前会保存设置）
        QTimer.singleShot(500, self.quit_app)

    def closeEvent(self, event):
        """点击关闭时最小化到系统托盘而不是退出。"""
        if not self._really_quit:
            event.ignore()
            self.hide()
            self._sync_walk_timer()
            if self.tray is not None and not self._tray_notice_shown:
                self._tray_notice_shown = True
                self.tray.showMessage(
                    "桌面宠物",
                    "已最小化到系统托盘，右键托盘图标可显示或退出。",
                    QSystemTrayIcon.Information,
                    3000,
                )
        else:
            event.accept()

    @staticmethod
    def _make_tray_icon():
        """生成一个橙色圆形“宠”字托盘图标。"""
        pixmap = QPixmap(64, 64)
        pixmap.fill(Qt.transparent)
        painter = QPainter(pixmap)
        painter.setRenderHint(QPainter.Antialiasing)
        painter.setPen(Qt.NoPen)
        painter.setBrush(QBrush(ORANGE))
        painter.drawEllipse(4, 4, 56, 56)
        painter.setPen(Qt.white)
        painter.setFont(QFont("Microsoft YaHei", 24, QFont.Bold))
        painter.drawText(pixmap.rect(), Qt.AlignCenter, "宠")
        painter.end()
        return QIcon(pixmap)


def main():
    """程序入口。"""
    # 高 DPI 支持（必须在创建 QApplication 之前设置）
    QApplication.setAttribute(Qt.AA_EnableHighDpiScaling, True)
    QApplication.setAttribute(Qt.AA_UseHighDpiPixmaps, True)

    app = QApplication(sys.argv)
    app.setQuitOnLastWindowClosed(False)  # 隐藏到托盘时不退出
    app.setApplicationName("桌面宠物")
    app.setFont(QFont("Microsoft YaHei", 9))

    # 确保 gifs / texts / audio / 语音包和文字 / ui 文件夹存在
    if not os.path.isdir(GIF_DIR):
        os.makedirs(GIF_DIR, exist_ok=True)
        print("[提示] 已创建 gifs 文件夹，请将十张 GIF 放入其中。")
    if not os.path.isdir(TEXT_DIR):
        os.makedirs(TEXT_DIR, exist_ok=True)
        print("[提示] 已创建 texts 文件夹，请放入对话框文字 .txt 文件。")
    if not os.path.isdir(AUDIO_DIR):
        os.makedirs(AUDIO_DIR, exist_ok=True)
        print("[提示] 已创建 audio 文件夹，放入 mp3/wav 音频后点击气泡会自动播放。")
    if not os.path.isdir(VOICE_DIR):
        os.makedirs(VOICE_DIR, exist_ok=True)
        print("[提示] 已创建 语音包和文字 文件夹，请放入同名 .txt 与 .wav 文件（文字与语音自动配对）。")
    if not os.path.isdir(UI_DIR):
        os.makedirs(UI_DIR, exist_ok=True)
        print("[提示] 已创建 ui 文件夹，放入 1-7.png 后气泡会自动装饰（1/2 角标、3-7 半透明贴纸）。")
    if not os.path.isdir(SONGS_DIR):
        os.makedirs(SONGS_DIR, exist_ok=True)
        print("[提示] 已创建 夏日活动主题曲 文件夹，放入 mp3 后“开始放歌！”会随机播放。")

    pet = DesktopPet()
    pet.show()
    sys.exit(app.exec_())


if __name__ == "__main__":
    main()
