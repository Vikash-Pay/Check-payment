import asyncio
from asyncio import subprocess
import aiohttp
import os
import sys
import logging
import aiofiles 
import subprocess
import psutil
import aiosqlite
import hashlib
import time
import shutil
import mimetypes
from datetime import datetime, timedelta
from pathlib import Path
from typing import Optional, Dict, Any, List, Tuple
import re

from aiogram import Bot, Dispatcher, types, F
from aiogram.filters import Command
from aiogram.types import InlineKeyboardMarkup, InlineKeyboardButton, FSInputFile
from aiogram.fsm.storage.memory import MemoryStorage
from aiogram.fsm.state import State, StatesGroup
from aiogram.fsm.context import FSMContext
from dotenv import load_dotenv

load_dotenv()

# Configure logging with rotation
from logging.handlers import RotatingFileHandler

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        RotatingFileHandler(
            'bot.log',
            maxBytes=10*1024*1024,
            backupCount=5
        ),
        logging.StreamHandler()
    ]
)
logger = logging.getLogger(__name__)

# Configuration
class Config:
    MAX_FILE_SIZE = 50 * 1024 * 1024  # 50MB
    ALLOWED_EXTENSIONS = {'py', 'js', 'zip'}
    SCRIPT_TIMEOUT = 30  # seconds
    FREE_USER_LIMIT = 20
    SUBSCRIBED_USER_LIMIT = 50
    ADMIN_LIMIT = 999
    OWNER_LIMIT = float('inf')
    CLEANUP_DAYS = 30
    BROADCAST_BATCH_SIZE = 50
    BROADCAST_DELAY = 0.1
    RATE_LIMIT_WINDOW = 60
    RATE_LIMIT_MAX_REQUESTS = 30
    DATABASE_PATH = 'bot_data.db'
    DATABASE_TIMEOUT = 30  # seconds
    TELEGRAM_MESSAGE_LIMIT = 4096
    BROADCAST_MESSAGE_LIMIT = 4000
    SCRIPT_OUTPUT_LIMIT = 2000
    LOG_COMPRESSION = False
    MAX_RUNNING_SCRIPTS = 5

# Security functions
def sanitize_filename(filename: str) -> str:
    """Remove dangerous characters from filename."""
    if not filename or len(filename.strip()) == 0:
        return "unnamed_file"
    
    # Remove path traversal
    filename = os.path.basename(filename)
    
    # Remove dangerous characters
    dangerous_chars = ['..', '/', '\\', ':', '*', '?', '"', '<', '>', '|', ';', '&', '$', '`']
    for char in dangerous_chars:
        filename = filename.replace(char, '_')
    
    # Limit length
    if len(filename) > 255:
        name, ext = os.path.splitext(filename)
        filename = name[:200] + ext
    
    return filename

def sanitize_search_query(query: str) -> str:
    """Sanitize search query."""
    # Remove SQL injection characters
    dangerous = ["'", '"', ';', '--', '/*', '*/', 'union', 'select', 'insert', 'delete', 'update', 'drop']
    sanitized = query
    for danger in dangerous:
        sanitized = sanitized.replace(danger, '')
    
    # Limit length
    if len(sanitized) > 100:
        sanitized = sanitized[:100]
    
    return sanitized.strip()

def validate_file_path(file_path: Path, user_id: int) -> bool:
    """Validate file path is within user directory."""
    try:
        user_dir = Path(f"upload_bots/{user_id}").resolve()
        file_path_resolved = file_path.resolve()
        return str(file_path_resolved).startswith(str(user_dir))
    except:
        return False

def validate_telegram_id(user_id: int) -> bool:
    """Validate if ID looks like a valid Telegram ID."""
    return isinstance(user_id, int) and user_id > 0

# Validate environment
TOKEN = os.getenv('BOT_TOKEN')
OWNER_ID_STR = os.getenv('OWNER_ID')
ADMIN_ID_STR = os.getenv('ADMIN_ID')
YOUR_USERNAME = os.getenv('YOUR_USERNAME')
UPDATE_CHANNEL = os.getenv('UPDATE_CHANNEL')

if not TOKEN:
    logger.error("BOT_TOKEN not found!")
    raise ValueError("BOT_TOKEN is required.")

if not OWNER_ID_STR or not ADMIN_ID_STR:
    logger.error("OWNER_ID or ADMIN_ID not found!")
    raise ValueError("OWNER_ID and ADMIN_ID are required.")

try:
    OWNER_ID = int(OWNER_ID_STR)
    ADMIN_ID = int(ADMIN_ID_STR)
except ValueError:
    logger.error("OWNER_ID or ADMIN_ID must be valid integers!")
    raise

if not validate_telegram_id(OWNER_ID) or not validate_telegram_id(ADMIN_ID):
    logger.error("Invalid Telegram ID format!")
    raise ValueError("OWNER_ID and ADMIN_ID must be valid Telegram IDs.")

YOUR_USERNAME = YOUR_USERNAME or '@DarkConflig'
UPDATE_CHANNEL = UPDATE_CHANNEL or 'https://t.me/+ONY2u-Ubz-o0NWRl'

BASE_DIR = Path(__file__).parent.absolute()
UPLOAD_BOTS_DIR = BASE_DIR / 'upload_bots'
IROTECH_DIR = BASE_DIR / 'inf'
DATABASE_PATH = IROTECH_DIR / Config.DATABASE_PATH
BACKUP_DIR = BASE_DIR / 'backups'

UPLOAD_BOTS_DIR.mkdir(exist_ok=True, parents=True)
IROTECH_DIR.mkdir(exist_ok=True, parents=True)
BACKUP_DIR.mkdir(exist_ok=True, parents=True)

bot = Bot(token=TOKEN)
dp = Dispatcher(storage=MemoryStorage())

# States
class UploadStates(StatesGroup):
    waiting_for_file = State()
    waiting_for_broadcast = State()
    waiting_for_admin_id = State()
    waiting_for_ban_user = State()
    waiting_for_unban_user = State()
    waiting_for_search = State()
    waiting_for_premium = State()

# Global state
bot_scripts = {}
user_subscriptions = {}
user_files = {}
user_favorites = {}
banned_users = set()
active_users = set()
admin_ids = {ADMIN_ID, OWNER_ID}
bot_locked = False
bot_stats = {'total_uploads': 0, 'total_downloads': 0, 'total_runs': 0, 'total_users': 0}

# Rate limiting with cleanup
class RateLimiter:
    def __init__(self):
        self.requests = {}
        self.last_cleanup = time.time()
    
    def _cleanup_old_entries(self):
        """Clean up old rate limit entries."""
        current_time = time.time()
        if current_time - self.last_cleanup > 3600:  # Cleanup every hour
            old_keys = []
            for key, data in self.requests.items():
                if current_time - data['window_start'] > Config.RATE_LIMIT_WINDOW * 10:  # 10 windows old
                    old_keys.append(key)
            
            for key in old_keys:
                del self.requests[key]
            
            self.last_cleanup = current_time
    
    async def check_limit(self, user_id: int, endpoint: str) -> bool:
        """Check rate limit for user and endpoint."""
        self._cleanup_old_entries()
        
        current_time = time.time()
        key = f"{user_id}:{endpoint}"
        
        if key not in self.requests:
            self.requests[key] = {'count': 1, 'window_start': current_time}
            return True
        
        request_data = self.requests[key]
        
        if current_time - request_data['window_start'] > Config.RATE_LIMIT_WINDOW:
            request_data['count'] = 1
            request_data['window_start'] = current_time
            return True
        
        if request_data['count'] >= Config.RATE_LIMIT_MAX_REQUESTS:
            return False
        
        request_data['count'] += 1
        return True

rate_limiter = RateLimiter()

# Database functions with timeout
async def execute_db_query(query: str, params: tuple = (), fetch_one: bool = False, fetch_all: bool = False):
    """Execute database query with timeout."""
    try:
        async with aiosqlite.connect(DATABASE_PATH, timeout=Config.DATABASE_TIMEOUT) as conn:
            conn.row_factory = aiosqlite.Row
            cursor = await conn.execute(query, params)
            
            if fetch_one:
                result = await cursor.fetchone()
            elif fetch_all:
                result = await cursor.fetchall()
            else:
                result = None
            
                      # Only commit for write operations
            if query.strip().upper().startswith(('INSERT', 'UPDATE', 'DELETE', 'REPLACE')):
                await conn.commit()
            return result
    except Exception as e:
        logger.error(f"Database error: {e}", exc_info=True)
        raise

async def init_db():
    """Initialize database tables."""
    try:
        await execute_db_query('''CREATE TABLE IF NOT EXISTS subscriptions
                                 (user_id INTEGER PRIMARY KEY, expiry TEXT)''')
        await execute_db_query('''CREATE TABLE IF NOT EXISTS user_files
                                 (user_id INTEGER, file_name TEXT, file_type TEXT, upload_date TEXT,
                                  file_size INTEGER, file_hash TEXT,
                                  PRIMARY KEY (user_id, file_name))''')
        await execute_db_query('''CREATE TABLE IF NOT EXISTS active_users
                                 (user_id INTEGER PRIMARY KEY, join_date TEXT, last_active TEXT,
                                  username TEXT, first_name TEXT, last_name TEXT)''')
        await execute_db_query('''CREATE TABLE IF NOT EXISTS admins
                                 (user_id INTEGER PRIMARY KEY, added_by INTEGER, added_date TEXT)''')
        await execute_db_query('''CREATE TABLE IF NOT EXISTS banned_users
                                 (user_id INTEGER PRIMARY KEY, banned_date TEXT, reason TEXT,
                                  banned_by INTEGER)''')
        await execute_db_query('''CREATE TABLE IF NOT EXISTS favorites
                                 (user_id INTEGER, file_name TEXT, added_date TEXT,
                                  PRIMARY KEY (user_id, file_name))''')
        await execute_db_query('''CREATE TABLE IF NOT EXISTS bot_stats
                                 (stat_name TEXT PRIMARY KEY, stat_value INTEGER)''')
        await execute_db_query('''CREATE TABLE IF NOT EXISTS running_scripts
                                 (user_id INTEGER, file_name TEXT, pid INTEGER, start_time TEXT,
                                  PRIMARY KEY (user_id, file_name))''')
        await execute_db_query('''CREATE TABLE IF NOT EXISTS db_version
                                 (version INTEGER PRIMARY KEY)''')
        
        now = datetime.now().isoformat()
        await execute_db_query('INSERT OR IGNORE INTO admins (user_id, added_by, added_date) VALUES (?, ?, ?)', 
                              (OWNER_ID, OWNER_ID, now))
        if ADMIN_ID != OWNER_ID:
            await execute_db_query('INSERT OR IGNORE INTO admins (user_id, added_by, added_date) VALUES (?, ?, ?)', 
                                  (ADMIN_ID, OWNER_ID, now))
        
        for stat in ['total_uploads', 'total_downloads', 'total_runs', 'total_users']:
            await execute_db_query('INSERT OR IGNORE INTO bot_stats (stat_name, stat_value) VALUES (?, 0)', (stat,))
        
        await execute_db_query('INSERT OR IGNORE INTO db_version (version) VALUES (1)', ())
        
        logger.info("Database initialized successfully.")
    except Exception as e:
        logger.error(f"Database initialization error: {e}", exc_info=True)

async def migrate_db():
    """Run database migrations with version tracking."""
    try:
        result = await execute_db_query('SELECT version FROM db_version', fetch_one=True)
        current_version = result['version'] if result else 1
        
        # Future migrations can be added here with version checks
        # if current_version == 1:
        #     await execute_db_query('ALTER TABLE ...')
        #     await execute_db_query('UPDATE db_version SET version = 2')
        #     current_version = 2
        
        logger.info(f"Database migrations completed. Current version: {current_version}")
    except Exception as e:
        logger.error(f"Database migration error: {e}", exc_info=True)

async def load_data():
    """Load data from database."""
    try:
        # Load subscriptions
        result = await execute_db_query('SELECT user_id, expiry FROM subscriptions', fetch_all=True)
        for row in result:
            try:
                user_subscriptions[row['user_id']] = {'expiry': datetime.fromisoformat(row['expiry'])}
            except:
                pass
        
        # Load user files
        result = await execute_db_query('SELECT user_id, file_name, file_type FROM user_files', fetch_all=True)
        for row in result:
            user_id = row['user_id']
            if user_id not in user_files:
                user_files[user_id] = []
            user_files[user_id].append((row['file_name'], row['file_type']))
        
        # Load active users
        result = await execute_db_query('SELECT user_id FROM active_users', fetch_all=True)
        for row in result:
            active_users.add(row['user_id'])
        
        # Load admins
        result = await execute_db_query('SELECT user_id FROM admins', fetch_all=True)
        for row in result:
            admin_ids.add(row['user_id'])
        
        # Load banned users
        result = await execute_db_query('SELECT user_id FROM banned_users', fetch_all=True)
        for row in result:
            banned_users.add(row['user_id'])
        
        # Load favorites
        result = await execute_db_query('SELECT user_id, file_name FROM favorites', fetch_all=True)
        for row in result:
            user_id = row['user_id']
            if user_id not in user_favorites:
                user_favorites[user_id] = []
            user_favorites[user_id].append(row['file_name'])
        
        # Load bot stats
        result = await execute_db_query('SELECT stat_name, stat_value FROM bot_stats', fetch_all=True)
        for row in result:
            bot_stats[row['stat_name']] = row['stat_value']
        
        logger.info(f"Data loaded: {len(active_users)} users, {len(banned_users)} banned, {len(admin_ids)} admins.")
    except Exception as e:
        logger.error(f"Error loading data: {e}", exc_info=True)

async def update_user_activity(user_id: int, username: str, first_name: str, last_name: str):
    """Update user activity in database."""
    try:
        now = datetime.now().isoformat()
        await execute_db_query('''INSERT OR REPLACE INTO active_users 
                                (user_id, join_date, last_active, username, first_name, last_name) 
                                VALUES (?, COALESCE((SELECT join_date FROM active_users WHERE user_id = ?), ?), ?, ?, ?, ?)''',
                             (user_id, user_id, now, now, username, first_name, last_name))
    except Exception as e:
        logger.error(f"Error updating user activity: {e}", exc_info=True)

async def save_user_file(user_id: int, file_name: str, file_type: str, file_size: int, file_hash: str):
    """Save file info to database."""
    try:
        upload_date = datetime.now().isoformat()
        await execute_db_query('''INSERT OR REPLACE INTO user_files 
                                (user_id, file_name, file_type, upload_date, file_size, file_hash) 
                                VALUES (?, ?, ?, ?, ?, ?)''',
                             (user_id, file_name, file_type, upload_date, file_size, file_hash))
        return True
    except Exception as e:
        logger.error(f"Error saving user file: {e}", exc_info=True)
        return False

async def delete_user_file(user_id: int, file_name: str):
    """Delete file from database."""
    try:
        await execute_db_query('DELETE FROM user_files WHERE user_id = ? AND file_name = ?', (user_id, file_name))
        await execute_db_query('DELETE FROM favorites WHERE user_id = ? AND file_name = ?', (user_id, file_name))
        
        if user_id in user_files:
            user_files[user_id] = [f for f in user_files[user_id] if f[0] != file_name]
        
        if user_id in user_favorites and file_name in user_favorites[user_id]:
            user_favorites[user_id].remove(file_name)
        
        return True
    except Exception as e:
        logger.error(f"Error deleting user file: {e}", exc_info=True)
        return False

def get_user_file_limit(user_id: int) -> int:
    """Get file upload limit for user."""
    if user_id == OWNER_ID: 
        return Config.OWNER_LIMIT
    if user_id in admin_ids: 
        return Config.ADMIN_LIMIT
    if user_id in user_subscriptions and user_subscriptions[user_id]['expiry'] > datetime.now():
        return Config.SUBSCRIBED_USER_LIMIT
    return Config.FREE_USER_LIMIT

# Rate limiting middleware
@dp.update.middleware()
async def rate_limit_middleware(handler, event, data):
    """Rate limiting middleware for all updates."""
    if hasattr(event, 'from_user'):
        user_id = event.from_user.id
        if user_id not in admin_ids:
            endpoint = type(event).__name__
            if not await rate_limiter.check_limit(user_id, endpoint):
                if isinstance(event, types.Message):
                    await event.answer("⚠️ Rate limit exceeded. Please try again later.")
                elif isinstance(event, types.CallbackQuery):
                    await event.answer("Rate limit exceeded!", show_alert=True)
                return
    return await handler(event, data)

# Check bot lock for all user functions
def check_bot_locked(user_id: int) -> bool:
    """Check if bot is locked and user is not admin."""
    return bot_locked and user_id not in admin_ids

# Command handlers
@dp.message(Command("start"))
async def cmd_start(message: types.Message):
    user_id = message.from_user.id
    
    if user_id in banned_users:
        await message.answer("🚫 <b>You are banned from using this bot!</b>\n\nContact admin for more info.", parse_mode="HTML")
        return
    
    if check_bot_locked(user_id):
        await message.answer("🔒 <b>Bot is currently locked for maintenance.</b>\n\nPlease try again later.")
        return
    
    active_users.add(user_id)
    await update_user_activity(user_id, message.from_user.username, message.from_user.first_name, message.from_user.last_name)
    
    welcome_text = f"""
╔═══════════════════════╗
    🌟 <b>WELCOME TO FILE HOST BOT</b> 🌟
╚═══════════════════════╝

👋 <b>Hi,</b> {message.from_user.full_name}!

🆔 <b>Your ID:</b> <code>{user_id}</code>
📦 <b>Upload Limit:</b> {get_user_file_limit(user_id)} files
💎 <b>Account:</b> {'Premium ✨' if user_id in user_subscriptions else 'Free 🆓'}

━━━━━━━━━━━━━━━━━━━━
<b>🎯 FREE USER FEATURES:</b>

📤 <b>Upload Files</b> - Upload Python, JS, ZIP files
📁 <b>Manage Files</b> - View, delete, organize
⭐ <b>Add Favorites</b> - Quick access to files
🔍 <b>Search Files</b> - Find files easily
▶️ <b>Run Scripts</b> - Execute Python/JS code
🛑 <b>Stop Scripts</b> - Control running code
📊 <b>View Stats</b> - Your usage statistics
⚡ <b>Speed Test</b> - Check bot response
📥 <b>Download Files</b> - Get your files
💾 <b>File Info</b> - Size, type, date details
ℹ️ <b>Help & Support</b> - Get assistance
🎯 <b>Feature List</b> - Explore all features

━━━━━━━━━━━━━━━━━━━━
<b>✨ Start exploring now! ✨</b>
"""
    
    await message.answer(welcome_text, reply_markup=get_main_keyboard(user_id), parse_mode="HTML")

def get_main_keyboard(user_id: int) -> InlineKeyboardMarkup:
    if user_id in admin_ids:
        keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="📢 Updates", url=UPDATE_CHANNEL)],
            [InlineKeyboardButton(text="📤 Upload File", callback_data="upload_file"),
             InlineKeyboardButton(text="📁 My Files", callback_data="check_files")],
            [InlineKeyboardButton(text="⭐ Favorites", callback_data="my_favorites"),
             InlineKeyboardButton(text="🔍 Search Files", callback_data="search_files")],
            [InlineKeyboardButton(text="⚡ Bot Speed", callback_data="bot_speed"),
             InlineKeyboardButton(text="📊 My Stats", callback_data="statistics")],
            [InlineKeyboardButton(text="ℹ️ Help & Info", callback_data="help_info"),
             InlineKeyboardButton(text="🎯 Features", callback_data="all_features")],
            [InlineKeyboardButton(text="👨‍💼 Admin Panel", callback_data="admin_panel"),
             InlineKeyboardButton(text="💬 Contact", url=f"https://t.me/{YOUR_USERNAME.replace('@', '')}")]
        ])
    else:
        keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="📢 Updates Channel", url=UPDATE_CHANNEL)],
            [InlineKeyboardButton(text="📤 Upload File", callback_data="upload_file"),
             InlineKeyboardButton(text="📁 My Files", callback_data="check_files")],
            [InlineKeyboardButton(text="⭐ Favorites", callback_data="my_favorites"),
             InlineKeyboardButton(text="🔍 Search Files", callback_data="search_files")],
            [InlineKeyboardButton(text="⚡ Bot Speed", callback_data="bot_speed"),
             InlineKeyboardButton(text="📊 My Stats", callback_data="statistics")],
            [InlineKeyboardButton(text="💎 Get Premium", callback_data="get_premium"),
             InlineKeyboardButton(text="ℹ️ Help", callback_data="help_info")],
            [InlineKeyboardButton(text="🎯 Features", callback_data="all_features"),
             InlineKeyboardButton(text="💬 Contact Owner", url=f"https://t.me/{YOUR_USERNAME.replace('@', '')}")]
        ])
    return keyboard

@dp.callback_query(F.data == "back_to_main")
async def callback_back_to_main(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if check_bot_locked(user_id):
        await callback.answer("🔒 Bot is locked for maintenance!", show_alert=True)
        return
    
    welcome_text = f"""
╔═══════════════════════╗
    🏠 <b>MAIN MENU</b> 🏠
╚═══════════════════════╝

👤 <b>User:</b> {callback.from_user.full_name}
🆔 <b>ID:</b> <code>{user_id}</code>
📦 <b>Files:</b> {len(user_files.get(user_id, []))}/{get_user_file_limit(user_id)}

Use buttons below to navigate 👇
"""
    await callback.message.edit_text(welcome_text, reply_markup=get_main_keyboard(user_id), parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "upload_file")
async def callback_upload_file(callback: types.CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    
    if check_bot_locked(user_id):
        await callback.answer("🔒 Bot is locked for maintenance!", show_alert=True)
        return
    
    current_files = len(user_files.get(user_id, []))
    limit = get_user_file_limit(user_id)
    
    if current_files >= limit:
        await callback.answer(f"❌ You've reached your limit of {limit} files!", show_alert=True)
        return
    
    upload_text = f"""
╔═══════════════════════╗
    📤 <b>UPLOAD FILES</b> 📤
╚═══════════════════════╝

📊 <b>Current Usage:</b> {current_files}/{limit} files

📝 <b>Supported Formats:</b>
🐍 Python (.py)
🟨 JavaScript (.js)
📦 ZIP Archives (.zip)

━━━━━━━━━━━━━━━━━━━━
<b>💡 How to Upload:</b>

1️⃣ Send your file to the bot
2️⃣ Wait for upload confirmation
3️⃣ File will be saved automatically

⚡ <b>Upload limit:</b> {limit} files
🔥 <b>Quick & Easy!</b>
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    
    await state.set_state(UploadStates.waiting_for_file)
    await callback.message.edit_text(upload_text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer("📤 Ready to receive your file...")

@dp.message(UploadStates.waiting_for_file)
async def handle_file_upload(message: types.Message, state: FSMContext):
    user_id = message.from_user.id
    
    if check_bot_locked(user_id):
        await message.answer("🔒 Bot is locked for maintenance!")
        await state.clear()
        return
    
    if not message.document:
        await message.answer("❌ Please send a valid file (Python, JavaScript, or ZIP).")
        return
    
    file_name = sanitize_filename(message.document.file_name)
    
    if not file_name:
        await message.answer("❌ Invalid filename!")
        await state.clear()
        return
    
    # Check file has extension
    if '.' not in file_name:
        await message.answer("❌ File must have an extension (.py, .js, .zip)")
        await state.clear()
        return
    
    # Check file size
    if message.document.file_size is None:
        await message.answer("❌ Unable to determine file size.")
        await state.clear()
        return
    
    if message.document.file_size > Config.MAX_FILE_SIZE:
        await message.answer(f"❌ File too large! Maximum size is {Config.MAX_FILE_SIZE // 1024 // 1024}MB.")
        await state.clear()
        return
    
    file_ext = file_name.split('.')[-1].lower()
    
    if file_ext not in Config.ALLOWED_EXTENSIONS:
        await message.answer("❌ Unsupported file type! Please send .py, .js, or .zip files only.")
        await state.clear()
        return
    
    current_files = len(user_files.get(user_id, []))
    limit = get_user_file_limit(user_id)
    
    if current_files >= limit:
        await message.answer(f"❌ You've reached your limit of {limit} files!")
        await state.clear()
        return
    
    file_type = file_ext
    
    try:
        user_dir = UPLOAD_BOTS_DIR / str(user_id)
        user_dir.mkdir(exist_ok=True)
        
        file_path = user_dir / file_name
        
        # Download file
        await bot.download(message.document, destination=file_path)
        
        # Validate file path
        if not validate_file_path(file_path, user_id):
            await message.answer("❌ Invalid file path!")
            file_path.unlink(missing_ok=True)
            await state.clear()
            return
        
        # Check MIME type as additional security
        mime_type, _ = mimetypes.guess_type(file_path)
        if mime_type and file_ext == 'py' and 'python' not in mime_type:
            logger.warning(f"Suspicious file: {file_name} has MIME type {mime_type}")
        
              # Get file info
        file_size = file_path.stat().st_size
        
        # Calculate file hash using SHA256
        with open(file_path, 'rb') as f:
            file_data = f.read()
        file_hash = hashlib.sha256(file_data).hexdigest()
        
        # Save to database
        
        # Save to database
        if await save_user_file(user_id, file_name, file_type, file_size, file_hash):
            # Update in-memory data
            if user_id not in user_files:
                user_files[user_id] = []
            user_files[user_id].append((file_name, file_type))
            
            # Update stats
            bot_stats['total_uploads'] = bot_stats.get('total_uploads', 0) + 1
            
            await message.answer(f"""
✅ <b>File Uploaded Successfully!</b>

📁 <b>File Name:</b> <code>{file_name}</code>
📊 <b>File Type:</b> {file_type.upper()}
💾 <b>File Size:</b> {file_size / 1024:.2f} KB
🔐 <b>File Hash:</b> <code>{file_hash[:16]}...</code>

📦 <b>Your Files:</b> {len(user_files[user_id])}/{limit}
""", parse_mode="HTML")
        else:
            await message.answer("❌ Error saving file to database.")
        
        await state.clear()
        
    except Exception as e:
        logger.error(f"Error uploading file: {e}", exc_info=True)
        await message.answer("❌ Error uploading file. Please try again.")
        await state.clear()

@dp.callback_query(F.data == "check_files")
async def callback_check_files(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if check_bot_locked(user_id):
        await callback.answer("🔒 Bot is locked for maintenance!", show_alert=True)
        return
    
    files = user_files.get(user_id, [])
    
    if not files:
        text = """
╔═══════════════════════╗
    📁 <b>MY FILES</b> 📁
╚═══════════════════════╝

📭 <b>No files found!</b>

Upload your first file to get started! 🚀
"""
        back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="📤 Upload File", callback_data="upload_file")],
            [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
        ])
    else:
        text = f"""
╔═══════════════════════╗
    📁 <b>MY FILES ({len(files)})</b> 📁
╚═══════════════════════╝

"""
        buttons = []
        for i, (file_name, file_type) in enumerate(files, 1):
            icon = "🐍" if file_type == "py" else "🟨" if file_type == "js" else "📦"
            text += f"{i}. {icon} <code>{file_name}</code>\n"
            
            is_favorite = file_name in user_favorites.get(user_id, [])
            star = "⭐" if is_favorite else "☆"
            
            buttons.append([
                InlineKeyboardButton(text=f"▶️ Run {file_name[:15]}", callback_data=f"run_script:{file_name}"),
                InlineKeyboardButton(text=f"{star}", callback_data=f"toggle_fav:{file_name}")
            ])
            buttons.append([
                InlineKeyboardButton(text=f"ℹ️ Info {file_name[:15]}", callback_data=f"file_info:{file_name}"),
                InlineKeyboardButton(text=f"🗑️ Delete", callback_data=f"delete_file:{file_name}")
            ])
        
        buttons.append([InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")])
        back_keyboard = InlineKeyboardMarkup(inline_keyboard=buttons)
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data.startswith("toggle_fav:"))
async def callback_toggle_favorite(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if check_bot_locked(user_id):
        await callback.answer("🔒 Bot is locked for maintenance!", show_alert=True)
        return
    
    file_name = callback.data.split(":", 1)[1]
    
    try:
        if user_id not in user_favorites:
            user_favorites[user_id] = []
        
        if file_name in user_favorites[user_id]:
            user_favorites[user_id].remove(file_name)
            await execute_db_query('DELETE FROM favorites WHERE user_id = ? AND file_name = ?', (user_id, file_name))
            await callback.answer("❌ Removed from favorites")
        else:
            user_favorites[user_id].append(file_name)
            added_date = datetime.now().isoformat()
            await execute_db_query('INSERT OR REPLACE INTO favorites (user_id, file_name, added_date) VALUES (?, ?, ?)',
                                 (user_id, file_name, added_date))
            await callback.answer("⭐ Added to favorites")
        
        await callback_check_files(callback)
        
    except Exception as e:
        logger.error(f"Error toggling favorite: {e}", exc_info=True)
        await callback.answer("❌ Error updating favorites")

@dp.callback_query(F.data.startswith("file_info:"))
async def callback_file_info(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if check_bot_locked(user_id):
        await callback.answer("🔒 Bot is locked for maintenance!", show_alert=True)
        return
    
    file_name = callback.data.split(":", 1)[1]
    
    try:
        result = await execute_db_query('SELECT file_type, upload_date, file_size, file_hash FROM user_files WHERE user_id = ? AND file_name = ?', 
                                       (user_id, file_name), fetch_one=True)
        
        if not result:
            await callback.answer("❌ File not found!")
            return
        
        file_type = result['file_type']
        upload_date = result['upload_date']
        file_size = result['file_size']
        file_hash = result['file_hash']
        
        upload_dt = datetime.fromisoformat(upload_date)
        
        file_path = UPLOAD_BOTS_DIR / str(user_id) / file_name
        exists = file_path.exists()
        
        icon = "🐍" if file_type == "py" else "🟨" if file_type == "js" else "📦"
        
        text = f"""
╔═══════════════════════╗
    ℹ️ <b>FILE INFORMATION</b> ℹ️
╚═══════════════════════╝

{icon} <b>File Name:</b> <code>{file_name}</code>
📊 <b>File Type:</b> {file_type.upper()}
📅 <b>Upload Date:</b> {upload_dt.strftime('%Y-%m-%d %H:%M:%S')}
💾 <b>File Size:</b> {file_size / 1024:.2f} KB
🔐 <b>File Hash:</b> <code>{file_hash}</code>
📁 <b>File Status:</b> {'✅ Available' if exists else '❌ Not Found'}
"""
        
        buttons = [
            [InlineKeyboardButton(text="📥 Download", callback_data=f"download_file:{file_name}")],
            [InlineKeyboardButton(text="▶️ Run Script", callback_data=f"run_script:{file_name}"),
             InlineKeyboardButton(text="🗑️ Delete", callback_data=f"delete_file:{file_name}")],
            [InlineKeyboardButton(text="📁 Back to Files", callback_data="check_files")]
        ]
        
        back_keyboard = InlineKeyboardMarkup(inline_keyboard=buttons)
        await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
        
    except Exception as e:
        logger.error(f"Error getting file info: {e}", exc_info=True)
        await callback.answer("❌ Error getting file information")

@dp.callback_query(F.data.startswith("delete_file:"))
async def callback_delete_file(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if check_bot_locked(user_id):
        await callback.answer("🔒 Bot is locked for maintenance!", show_alert=True)
        return
    
    file_name = callback.data.split(":", 1)[1]
    
    try:
        file_path = UPLOAD_BOTS_DIR / str(user_id) / file_name
        if file_path.exists():
            # Validate path before deletion
            if validate_file_path(file_path, user_id):
                file_path.unlink()
        
        await delete_user_file(user_id, file_name)
        
        await callback.answer(f"✅ File '{file_name}' deleted successfully!")
        await callback_check_files(callback)
        
    except Exception as e:
        logger.error(f"Error deleting file: {e}", exc_info=True)
        await callback.answer("❌ Error deleting file")

@dp.callback_query(F.data.startswith("download_file:"))
async def callback_download_file(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if check_bot_locked(user_id):
        await callback.answer("🔒 Bot is locked for maintenance!", show_alert=True)
        return
    
    file_name = callback.data.split(":", 1)[1]
    
    file_path = UPLOAD_BOTS_DIR / str(user_id) / file_name
    
    if not file_path.exists():
        await callback.answer("❌ File not found!")
        return
    
    # Validate file path
    if not validate_file_path(file_path, user_id):
        await callback.answer("❌ Invalid file path!")
        return
    
    # Check file size
    try:
        file_size = file_path.stat().st_size
        if file_size > Config.MAX_FILE_SIZE:
            await callback.answer(f"❌ File too large ({file_size//1024//1024}MB)!", show_alert=True)
            return
    except:
        pass
    
    try:
        bot_stats['total_downloads'] = bot_stats.get('total_downloads', 0) + 1
        
        await callback.message.answer_document(
            document=FSInputFile(file_path),
            caption=f"📥 <b>File Download:</b> <code>{file_name}</code>\n👤 <b>User ID:</b> <code>{user_id}</code>",
            parse_mode="HTML"
        )
        await callback.answer()
        
    except Exception as e:
        logger.error(f"Error sending file: {e}", exc_info=True)
        await callback.answer("❌ Error downloading file")

async def run_script_async(file_path: Path, file_ext: str, timeout: int = Config.SCRIPT_TIMEOUT):
    """Run script asynchronously with timeout."""
    if file_ext == 'py':
        cmd = [sys.executable, str(file_path)]
    elif file_ext == 'js':
        cmd = ['node', str(file_path)]
    else:
        raise ValueError(f"Unsupported file extension: {file_ext}")
    
    try:
        process = await asyncio.create_subprocess_exec(
            *cmd,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE
        )
        
        try:
            stdout, stderr = await asyncio.wait_for(
                process.communicate(),
                timeout=timeout
            )
            
            return process.pid, process.returncode, stdout.decode('utf-8', errors='ignore'), stderr.decode('utf-8', errors='ignore')
            
        except asyncio.TimeoutError:
            process.terminate()
            try:
                await asyncio.wait_for(process.wait(), timeout=5)
            except asyncio.TimeoutError:
                process.kill()
                await process.wait()
            
            raise TimeoutError(f"Script execution timed out after {timeout} seconds")
            
    except Exception as e:
        raise Exception(f"Error executing script: {e}")

@dp.callback_query(F.data.startswith("run_script:"))
async def callback_run_script(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if check_bot_locked(user_id):
        await callback.answer("🔒 Bot is locked for maintenance!", show_alert=True)
        return
    
    # Check if user has too many running scripts
    user_scripts = bot_scripts.get(user_id, {})
    if len(user_scripts) >= Config.MAX_RUNNING_SCRIPTS:
        await callback.answer(f"❌ You can only run {Config.MAX_RUNNING_SCRIPTS} scripts at once.", show_alert=True)
        return
    
    file_name = callback.data.split(":", 1)[1]
    
    file_path = UPLOAD_BOTS_DIR / str(user_id) / file_name
    
    if not file_path.exists():
        await callback.answer("❌ File not found!")
        return
    
    # Validate file path
    if not validate_file_path(file_path, user_id):
        await callback.answer("❌ Invalid file path!")
        return
    
    try:
        file_ext = file_name.split('.')[-1].lower()
        
        if file_ext not in ['py', 'js']:
            await callback.answer("❌ Only Python and JavaScript files can be executed!")
            return
        
        pid, returncode, stdout, stderr = await run_script_async(file_path, file_ext)
        
        # Track script PID
        if user_id not in bot_scripts:
            bot_scripts[user_id] = {}
        bot_scripts[user_id][file_name] = pid
        
        # Save to database
        await execute_db_query('INSERT OR REPLACE INTO running_scripts (user_id, file_name, pid, start_time) VALUES (?, ?, ?, ?)',
                             (user_id, file_name, pid, datetime.now().isoformat()))
        
        bot_stats['total_runs'] = bot_stats.get('total_runs', 0) + 1
        
        # Truncate output for Telegram limits
        stdout_truncated = stdout[:Config.SCRIPT_OUTPUT_LIMIT]
        stderr_truncated = stderr[:Config.SCRIPT_OUTPUT_LIMIT//2]
        
        if len(stdout) > Config.SCRIPT_OUTPUT_LIMIT:
            stdout_truncated += "\n...[Output truncated due to size limit]..."
        
        if len(stderr) > Config.SCRIPT_OUTPUT_LIMIT//2:
            stderr_truncated += "\n...[Errors truncated due to size limit]..."
        
        output_text = f"""
╔═══════════════════════╗
    🚀 <b>SCRIPT OUTPUT</b> 🚀
╚═══════════════════════╝

📁 <b>File:</b> <code>{file_name}</code>
👤 <b>User ID:</b> <code>{user_id}</code>
📊 <b>Exit Code:</b> {returncode}
🆔 <b>PID:</b> {pid}

━━━━━━━━━━━━━━━━━━━━
<b>📤 STDOUT:</b>
<pre>{stdout_truncated if stdout else 'No output'}</pre>

<b>📥 STDERR:</b>
<pre>{stderr_truncated if stderr else 'No errors'}</pre>
"""
        
        buttons = [
            [InlineKeyboardButton(text="📁 My Files", callback_data="check_files"),
             InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
        ]
        
        back_keyboard = InlineKeyboardMarkup(inline_keyboard=buttons)
        
        await callback.message.answer(output_text[:Config.TELEGRAM_MESSAGE_LIMIT], reply_markup=back_keyboard, parse_mode="HTML")
        await callback.answer("✅ Script executed!")
        
    except TimeoutError as e:
        await callback.message.answer(f"⏰ {str(e)}")
    except Exception as e:
        logger.error(f"Error running script: {e}", exc_info=True)
        await callback.answer(f"❌ Error: {str(e)[:100]}")

@dp.message(Command("stop"))
async def cmd_stop_script(message: types.Message):
    user_id = message.from_user.id
    
    if not message.text or len(message.text.split()) < 2:
        await message.answer("Usage: /stop <pid>")
        return
    
    try:
        pid = int(message.text.split()[1])
        
        for uid, scripts in bot_scripts.items():
            for fname, spid in scripts.items():
                if spid == pid:
                    if uid != user_id and user_id not in admin_ids:
                        await message.answer("❌ You can only stop your own scripts!")
                        return
                    
                    try:
                        process = psutil.Process(pid)
                        process.terminate()
                        process.wait(timeout=5)
                        
                        if uid in bot_scripts and fname in bot_scripts[uid]:
                            del bot_scripts[uid][fname]
                        
                        await execute_db_query('DELETE FROM running_scripts WHERE pid = ?', (pid,))
                        
                        await message.answer(f"✅ Script stopped (PID: {pid})")
                        return
                        
                    except psutil.NoSuchProcess:
                        await message.answer(f"❌ No process with PID {pid}")
                        return
        
        await message.answer(f"❌ No running script found with PID {pid}")
        
    except ValueError:
        await message.answer("❌ Invalid PID. Please provide a number.")
    except Exception as e:
        logger.error(f"Error stopping script: {e}", exc_info=True)
        await message.answer("❌ Error stopping script")

@dp.callback_query(F.data == "my_favorites")
async def callback_my_favorites(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if check_bot_locked(user_id):
        await callback.answer("🔒 Bot is locked for maintenance!", show_alert=True)
        return
    
    favorites = user_favorites.get(user_id, [])
    
    if not favorites:
        text = """
╔═══════════════════════╗
    ⭐ <b>FAVORITES</b> ⭐
╚═══════════════════════╝

💭 No favorite files yet!

Add files to favorites for quick access! 🚀
"""
        buttons = [[InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]]
    else:
        text = f"""
╔═══════════════════════╗
    ⭐ <b>FAVORITES ({len(favorites)})</b> ⭐
╚═══════════════════════╝

"""
        buttons = []
        for i, file_name in enumerate(favorites, 1):
            text += f"{i}. ⭐ <code>{file_name}</code>\n"
            buttons.append([
                InlineKeyboardButton(text=f"▶️ {file_name[:20]}", callback_data=f"run_script:{file_name}"),
                InlineKeyboardButton(text=f"❌", callback_data=f"toggle_fav:{file_name}")
            ])
        
        buttons.append([InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")])
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=buttons)
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "search_files")
async def callback_search_files(callback: types.CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    
    if check_bot_locked(user_id):
        await callback.answer("🔒 Bot is locked for maintenance!", show_alert=True)
        return
    
    files = user_files.get(user_id, [])
    
    text = f"""
╔═══════════════════════╗
    🔍 <b>SEARCH FILES</b> 🔍
╚═══════════════════════╝

📊 <b>Total Files:</b> {len(files)}

<b>File Types:</b>
🐍 Python: {sum(1 for f in files if f[1] == 'py')}
🟨 JavaScript: {sum(1 for f in files if f[1] == 'js')}
📦 ZIP: {sum(1 for f in files if f[1] == 'zip')}

━━━━━━━━━━━━━━━━━━━━
<b>💡 How to search:</b>

Send me any keyword or part of filename!

Examples:
• <code>bot</code> - finds all files with "bot"
• <code>.py</code> - finds all Python files
• <code>test.js</code> - finds specific JS file
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📁 View All Files", callback_data="check_files")],
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    
    await state.set_state(UploadStates.waiting_for_search)
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.message(UploadStates.waiting_for_search)
async def handle_search_query(message: types.Message, state: FSMContext):
    user_id = message.from_user.id
    
    if check_bot_locked(user_id):
        await message.answer("🔒 Bot is locked for maintenance!")
        await state.clear()
        return
    
    query = sanitize_search_query(message.text.strip())
    
    if not query:
        await message.answer("❌ Please enter a search query.")
        return
    
    files = user_files.get(user_id, [])
    results = []
    
    for file_name, file_type in files:
        if query.lower() in file_name.lower():
            results.append((file_name, file_type))
    
    if not results:
        text = f"""
🔍 <b>SEARCH RESULTS</b>

❌ No files found for: <code>{query}</code>

Try a different keyword or check spelling.
"""
        buttons = [
            [InlineKeyboardButton(text="🔄 Search Again", callback_data="search_files"),
             InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
        ]
    else:
        text = f"""
╔═══════════════════════╗
    🔍 <b>SEARCH RESULTS</b> 🔍
╚═══════════════════════╝

<b>Query:</b> <code>{query}</code>
<b>Found:</b> {len(results)} file(s)

"""
        buttons = []
        for file_name, file_type in results:
            icon = "🐍" if file_type == "py" else "🟨" if file_type == "js" else "📦"
            text += f"• {icon} <code>{file_name}</code>\n"
            
            buttons.append([
                InlineKeyboardButton(text=f"▶️ {file_name[:15]}", callback_data=f"run_script:{file_name}"),
                InlineKeyboardButton(text=f"📥 Download", callback_data=f"download_file:{file_name}")
            ])
        
        buttons.append([
            InlineKeyboardButton(text="🔄 New Search", callback_data="search_files"),
            InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")
        ])
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=buttons)
    await message.answer(text, reply_markup=back_keyboard, parse_mode="HTML")
    await state.clear()

@dp.callback_query(F.data == "bot_speed")
async def callback_bot_speed(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if check_bot_locked(user_id):
        await callback.answer("🔒 Bot is locked for maintenance!", show_alert=True)
        return
    
    start_time = time.time()
    speed = (time.time() - start_time) * 1000
    
    if speed < 100:
        status = "🟢 Excellent"
        emoji = "🚀"
    elif speed < 300:
        status = "🟡 Good"
        emoji = "⚡"
    else:
        status = "🔴 Slow"
        emoji = "🐌"
    
    await callback.answer("⚡ Testing...")
    
    text = f"""
╔═══════════════════════╗
    ⚡ <b>SPEED TEST</b> ⚡
╚═══════════════════════╝

{emoji} <b>Response Time:</b> {speed:.2f}ms
📊 <b>Status:</b> {status}

🖥️ <b>Server Info:</b>
• CPU: {psutil.cpu_percent()}%
• Memory: {psutil.virtual_memory().percent}%
• Disk: {psutil.disk_usage('/').percent}%
• Uptime: Online ✅

✨ Bot is running smoothly!
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔄 Test Again", callback_data="bot_speed"),
         InlineKeyboardButton(text="🏠 Home", callback_data="back_to_main")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")

@dp.callback_query(F.data == "statistics")
async def callback_statistics(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if check_bot_locked(user_id):
        await callback.answer("🔒 Bot is locked for maintenance!", show_alert=True)
        return
    
    files = user_files.get(user_id, [])
    
    py_count = sum(1 for f in files if f[1] == 'py')
    js_count = sum(1 for f in files if f[1] == 'js')
    zip_count = sum(1 for f in files if f[1] == 'zip')
    
    total_size = 0
    user_dir = UPLOAD_BOTS_DIR / str(user_id)
    if user_dir.exists():
        for file in user_dir.iterdir():
            if file.is_file():
                total_size += file.stat().st_size
    
    text = f"""
╔═══════════════════════╗
    📊 <b>YOUR STATISTICS</b> 📊
╚═══════════════════════╝

👤 <b>User:</b> {callback.from_user.full_name}
🆔 <b>ID:</b> <code>{user_id}</code>
💎 <b>Status:</b> {'Premium ✨' if user_id in user_subscriptions else 'Free 🆓'}

━━━━━━━━━━━━━━━━━━━━
<b>📁 FILE STATS:</b>

📦 <b>Total Files:</b> {len(files)}
🐍 <b>Python Files:</b> {py_count}
🟨 <b>JavaScript Files:</b> {js_count}
📦 <b>ZIP Archives:</b> {zip_count}
💾 <b>Total Size:</b> {total_size / 1024 / 1024:.2f} MB

━━━━━━━━━━━━━━━━━━━━
<b>⭐ FAVORITES:</b>
❤️ <b>Favorite Files:</b> {len(user_favorites.get(user_id, []))}

━━━━━━━━━━━━━━━━━━━━
<b>🎯 ACCOUNT LIMITS:</b>
📤 <b>Upload Limit:</b> {get_user_file_limit(user_id)} files
📥 <b>Current Usage:</b> {len(files)} files
📈 <b>Available:</b> {get_user_file_limit(user_id) - len(files)} files
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔄 Refresh", callback_data="statistics"),
         InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "help_info")
async def callback_help_info(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if check_bot_locked(user_id):
        await callback.answer("🔒 Bot is locked for maintenance!", show_alert=True)
        return
    
    text = """
╔═══════════════════════╗
    ℹ️ <b>HELP & INFORMATION</b> ℹ️
╚═══════════════════════╝

<b>📚 AVAILABLE COMMANDS:</b>

• /start - Start the bot
• /stop <pid> - Stop running script
• /search <query> - Search files
• /stats - Show your statistics
• /help - Show this message

━━━━━━━━━━━━━━━━━━━━
<b>🎯 BOT FEATURES:</b>

• 📤 Upload files (.py, .js, .zip)
• 📁 Manage your files
• ⭐ Mark files as favorites
• 🔍 Search through files
• ▶️ Run Python/JS scripts
• 🛑 Stop running scripts
• 📥 Download your files
• 📊 View statistics
• ⚡ Speed test

━━━━━━━━━━━━━━━━━━━━
<b>⚠️ IMPORTANT NOTES:</b>

1. Max file size: 50MB
2. Supported: Python, JavaScript, ZIP
3. Scripts run with timeout
4. Keep backups of your files
5. Contact admin for issues

━━━━━━━━━━━━━━━━━━━━
<b>👥 SUPPORT:</b>

For help, contact: @DarkConflig
Join updates: @DarkConflig_Updates
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📢 Updates Channel", url=UPDATE_CHANNEL)],
        [InlineKeyboardButton(text="💬 Contact Owner", url=f"https://t.me/{YOUR_USERNAME.replace('@', '')}")],
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "all_features")
async def callback_all_features(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if check_bot_locked(user_id):
        await callback.answer("🔒 Bot is locked for maintenance!", show_alert=True)
        return
    
    text = """
╔══════════════════════════╗
    🎯 <b>ALL FEATURES</b> 🎯
╚══════════════════════════╝

<b>🌟 CORE FEATURES:</b>

📤 <b>File Upload</b> - Upload Python/JS/ZIP files
📁 <b>File Management</b> - View, delete, organize
⭐ <b>Favorites System</b> - Star important files
🔍 <b>Smart Search</b> - Find files instantly
▶️ <b>Script Runner</b> - Execute code directly
🛑 <b>Process Control</b> - Stop running scripts
📥 <b>File Download</b> - Get your files anytime
💾 <b>File Info</b> - Detailed file information

━━━━━━━━━━━━━━━━━━━━
<b>📊 ANALYTICS:</b>

📈 <b>User Statistics</b> - Track your usage
⚡ <b>Speed Test</b> - Check bot performance
📅 <b>Activity Logs</b> - View your history
🔢 <b>File Counters</b> - Monitor uploads

━━━━━━━━━━━━━━━━━━━━
<b>🔐 SECURITY:</b>

🔒 <b>File Hashing</b> - MD5 checksums
👮 <b>User Isolation</b> - Separate directories
🚫 <b>Ban System</b> - Admin control
🔑 <b>Access Control</b> - Permission levels

━━━━━━━━━━━━━━━━━━━━
<b>⚙️ ADMIN FEATURES:</b>

👥 <b>User Management</b> - View all users
📊 <b>Bot Analytics</b> - System statistics
🔧 <b>System Control</b> - Lock/restart bot
📢 <b>Broadcast</b> - Send messages to users
🗑️ <b>Cleanup Tools</b> - Remove old files
💾 <b>Backup System</b> - Database backups

━━━━━━━━━━━━━━━━━━━━
<b>🆓 FREE vs PREMIUM:</b>

<b>Free Users:</b>
• 20 file limit
• Basic features
• Standard support

<b>Premium Users:</b>
• 50 file limit
• Priority support
• All features unlocked
• Faster processing
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💎 Get Premium", callback_data="get_premium")],
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "get_premium")
async def callback_get_premium(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if check_bot_locked(user_id):
        await callback.answer("🔒 Bot is locked for maintenance!", show_alert=True)
        return
    
    text = """
╔═══════════════════════╗
    💎 <b>GET PREMIUM</b> 💎
╚═══════════════════════╝

<b>✨ PREMIUM BENEFITS:</b>

• 📦 <b>50 file limit</b> (vs 20 free)
• 🚀 <b>Priority processing</b>
• ⭐ <b>Premium badge</b>
• 🔓 <b>All features unlocked</b>
• 📞 <b>Priority support</b>
• ⚡ <b>Faster speeds</b>

━━━━━━━━━━━━━━━━━━━━
<b>💰 PRICING:</b>

• 1 Month: $5
• 3 Months: $12
• 6 Months: $20
• 1 Year: $35

━━━━━━━━━━━━━━━━━━━━
<b>🛒 HOW TO GET:</b>

1. Contact @DarkConflig
2. Choose your plan
3. Make payment
4. Get activated instantly!

━━━━━━━━━━━━━━━━━━━━
<b>💳 PAYMENT METHODS:</b>

• PayPal
• Crypto (USDT)
• Local payment methods
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="💬 Contact Owner", url=f"https://t.me/{YOUR_USERNAME.replace('@', '')}")],
        [InlineKeyboardButton(text="📢 Updates", url=UPDATE_CHANNEL)],
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

def get_admin_panel_keyboard() -> InlineKeyboardMarkup:
    keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="👥 User Stats", callback_data="admin_total_users"),
         InlineKeyboardButton(text="📁 Files Stats", callback_data="admin_total_files")],
        [InlineKeyboardButton(text="🚀 Running Scripts", callback_data="admin_running_scripts"),
         InlineKeyboardButton(text="💎 Premium Users", callback_data="admin_premium_users")],
        [InlineKeyboardButton(text="➕ Add Admin", callback_data="admin_add_admin"),
         InlineKeyboardButton(text="➖ Remove Admin", callback_data="admin_remove_admin")],
        [InlineKeyboardButton(text="🚫 Ban User", callback_data="admin_ban_user"),
         InlineKeyboardButton(text="✅ Unban User", callback_data="admin_unban_user")],
        [InlineKeyboardButton(text="📊 Bot Analytics", callback_data="admin_analytics"),
         InlineKeyboardButton(text="⚙️ System Info", callback_data="admin_system_status")],
        [InlineKeyboardButton(text="🔒 Lock/Unlock", callback_data="lock_bot"),
         InlineKeyboardButton(text="📢 Broadcast", callback_data="broadcast")],
        [InlineKeyboardButton(text="🗑️ Clean Files", callback_data="admin_clean_files"),
         InlineKeyboardButton(text="💾 Backup DB", callback_data="admin_backup_db")],
        [InlineKeyboardButton(text="📝 View Logs", callback_data="admin_view_logs"),
         InlineKeyboardButton(text="🔄 Restart Bot", callback_data="admin_restart_bot")],
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    return keyboard

@dp.callback_query(F.data == "admin_panel")
async def callback_admin_panel(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    text = f"""
╔═══════════════════════╗
    👨‍💼 <b>ADMIN PANEL</b> 👨‍💼
╚═══════════════════════╝

<b>Welcome, Admin!</b>

🆔 <b>Your ID:</b> <code>{user_id}</code>
👥 <b>Total Users:</b> {len(active_users)}
📁 <b>Total Files:</b> {sum(len(files) for files in user_files.values())}
🚀 <b>Running Scripts:</b> {sum(len(scripts) for scripts in bot_scripts.values())}
🔒 <b>Bot Status:</b> {'Locked 🔒' if bot_locked else 'Unlocked 🔓'}

━━━━━━━━━━━━━━━━━━━━
<b>⚙️ ADMIN CONTROLS:</b>

Use buttons below to manage the bot.
"""
    
    await callback.message.edit_text(text, reply_markup=get_admin_panel_keyboard(), parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "admin_total_users")
async def callback_admin_total_users(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    try:
        # Total users
        result = await execute_db_query('SELECT COUNT(*) as count FROM active_users', fetch_one=True)
        total_users = result['count']
        
        # Active last 7 days
        week_ago = (datetime.now() - timedelta(days=7)).isoformat()
        result = await execute_db_query('SELECT COUNT(*) as count FROM active_users WHERE last_active >= ?', (week_ago,), fetch_one=True)
        active_week = result['count']
        
        # New today
        today = datetime.now().strftime('%Y-%m-%d')
        result = await execute_db_query('SELECT COUNT(*) as count FROM active_users WHERE date(join_date) = ?', (today,), fetch_one=True)
        new_today = result['count']
        
        # Users with files
        result = await execute_db_query('SELECT COUNT(DISTINCT user_id) as count FROM user_files', fetch_one=True)
        users_with_files = result['count']
        
        text = f"""
╔═══════════════════════╗
    👥 <b>USER STATISTICS</b> 👥
╚═══════════════════════╝

📊 <b>User Analytics:</b>

👥 <b>Total Users:</b> {total_users}
📈 <b>Active (7 days):</b> {active_week}
🆕 <b>New Today:</b> {new_today}
📁 <b>Users with Files:</b> {users_with_files}
💎 <b>Premium Users:</b> {len(user_subscriptions)}
🚫 <b>Banned Users:</b> {len(banned_users)}
👑 <b>Admins:</b> {len(admin_ids)}

━━━━━━━━━━━━━━━━━━━━
<b>📈 GROWTH:</b>

• Daily growth: {new_today} users
• Active rate: {(active_week/total_users*100) if total_users > 0 else 0:.1f}% (7 days)
• File upload rate: {(users_with_files/total_users*100) if total_users > 0 else 0:.1f}%
"""
        
        back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="📊 Refresh", callback_data="admin_total_users")],
            [InlineKeyboardButton(text="🔙 Back", callback_data="admin_panel")]
        ])
        
        await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
        
    except Exception as e:
        logger.error(f"Error getting user stats: {e}", exc_info=True)
        await callback.answer("❌ Error getting statistics")

@dp.callback_query(F.data == "admin_total_files")
async def callback_admin_total_files(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    try:
        # Total files
        result = await execute_db_query('SELECT COUNT(*) as count FROM user_files', fetch_one=True)
        total_files = result['count']
        
        # Total size
        result = await execute_db_query('SELECT SUM(file_size) as total FROM user_files', fetch_one=True)
        total_size = result['total'] or 0
        
        # File types
        result = await execute_db_query('SELECT file_type, COUNT(*) as count FROM user_files GROUP BY file_type', fetch_all=True)
        file_types = [(row['file_type'], row['count']) for row in result]
        
        # Users with files
        result = await execute_db_query('SELECT COUNT(DISTINCT user_id) as count FROM user_files', fetch_one=True)
        users_with_files = result['count']
        
        # Uploaded today
        today = datetime.now().strftime('%Y-%m-%d')
        result = await execute_db_query('SELECT COUNT(*) as count FROM user_files WHERE date(upload_date) = ?', (today,), fetch_one=True)
        uploaded_today = result['count']
        
        text = f"""
╔═══════════════════════╗
    📁 <b>FILE STATISTICS</b> 📁
╚═══════════════════════╝

📊 <b>File Analytics:</b>

📦 <b>Total Files:</b> {total_files}
💾 <b>Total Size:</b> {total_size / 1024 / 1024 / 1024:.2f} GB
👥 <b>Users with Files:</b> {users_with_files}
📤 <b>Uploaded Today:</b> {uploaded_today}

━━━━━━━━━━━━━━━━━━━━
<b>📈 FILE TYPES:</b>
"""
        
        for file_type, count in file_types:
            icon = "🐍" if file_type == "py" else "🟨" if file_type == "js" else "📦"
            percentage = (count / total_files * 100) if total_files > 0 else 0
            text += f"• {icon} {file_type.upper()}: {count} ({percentage:.1f}%)\n"
        
        avg_files = total_files / users_with_files if users_with_files > 0 else 0
        avg_size = total_size / total_files if total_files > 0 else 0
        
        text += f"""
━━━━━━━━━━━━━━━━━━━━
<b>📊 AVERAGES:</b>

• Files per user: {avg_files:.1f} (active)
• Avg file size: {avg_size/1024:.1f} KB
• Daily uploads: {uploaded_today}
"""
        
        back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="🗑️ Clean Files", callback_data="admin_clean_files")],
            [InlineKeyboardButton(text="📊 Refresh", callback_data="admin_total_files")],
            [InlineKeyboardButton(text="🔙 Back", callback_data="admin_panel")]
        ])
        
        await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
        
    except Exception as e:
        logger.error(f"Error getting file stats: {e}", exc_info=True)
        await callback.answer("❌ Error getting statistics")

@dp.callback_query(F.data == "admin_running_scripts")
async def callback_admin_running_scripts(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    total_scripts = sum(len(scripts) for scripts in bot_scripts.values())
    
    if total_scripts == 0:
        text = """
╔═══════════════════════╗
    🚀 <b>RUNNING SCRIPTS</b> 🚀
╚═══════════════════════╝

📭 <b>No scripts are currently running.</b>

All scripts have finished execution.
"""
        buttons = []
    else:
        text = f"""
╔═══════════════════════╗
    🚀 <b>RUNNING SCRIPTS ({total_scripts})</b> 🚀
╚═══════════════════════╝

"""
        buttons = []
        script_count = 0
        
        for uid, scripts in bot_scripts.items():
            for fname, pid in scripts.items():
                script_count += 1
                text += f"{script_count}. 👤 {uid} | 📁 {fname} | 🆔 {pid}\n"
                
                buttons.append([
                    InlineKeyboardButton(text=f"🛑 Stop {pid}", callback_data=f"admin_stop_script:{pid}"),
                    InlineKeyboardButton(text=f"👁️ View {uid}", callback_data=f"admin_view_user:{uid}")
                ])
    
    buttons.append([
        InlineKeyboardButton(text="🔄 Refresh", callback_data="admin_running_scripts"),
        InlineKeyboardButton(text="🔙 Back", callback_data="admin_panel")
    ])
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=buttons)
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data.startswith("admin_stop_script:"))
async def callback_admin_stop_script(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    pid = int(callback.data.split(":", 1)[1])
    
    try:
        process = psutil.Process(pid)
        process.terminate()
        process.wait(timeout=5)
        
        # Remove from bot_scripts
        for uid, scripts in list(bot_scripts.items()):
            for fname, spid in list(scripts.items()):
                if spid == pid:
                    if uid in bot_scripts and fname in bot_scripts[uid]:
                        del bot_scripts[uid][fname]
                    break
        
        # Remove from database
        await execute_db_query('DELETE FROM running_scripts WHERE pid = ?', (pid,))
        
        await callback.answer(f"✅ Script {pid} stopped")
        await callback_admin_running_scripts(callback)
        
    except psutil.NoSuchProcess:
        await callback.answer(f"❌ No process with PID {pid}")
    except Exception as e:
        logger.error(f"Error stopping script: {e}", exc_info=True)
        await callback.answer(f"❌ Error: {str(e)}")

@dp.callback_query(F.data.startswith("admin_view_user:"))
async def callback_admin_view_user(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    target_id = int(callback.data.split(":", 1)[1])
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    try:
        # Get user info
        result = await execute_db_query('SELECT username, first_name, last_name, join_date, last_active FROM active_users WHERE user_id = ?', 
                                       (target_id,), fetch_one=True)
        
        if not result:
            text = f"❌ User {target_id} not found in database."
            buttons = []
        else:
            # Get user stats
            file_result = await execute_db_query('SELECT COUNT(*) as count FROM user_files WHERE user_id = ?', (target_id,), fetch_one=True)
            file_count = file_result['count']
            
            fav_result = await execute_db_query('SELECT COUNT(*) as count FROM favorites WHERE user_id = ?', (target_id,), fetch_one=True)
            fav_count = fav_result['count']
            
            premium_result = await execute_db_query('SELECT COUNT(*) as count FROM subscriptions WHERE user_id = ?', (target_id,), fetch_one=True)
            is_premium = premium_result['count'] > 0
            
            banned_result = await execute_db_query('SELECT COUNT(*) as count FROM banned_users WHERE user_id = ?', (target_id,), fetch_one=True)
            is_banned = banned_result['count'] > 0
            
            username = result['username'] or 'N/A'
            first_name = result['first_name'] or ''
            last_name = result['last_name'] or ''
            join_date = datetime.fromisoformat(result['join_date'])
            last_active = datetime.fromisoformat(result['last_active'])
            
            text = f"""
╔═══════════════════════╗
    👤 <b>USER DETAILS</b> 👤
╚═══════════════════════╝

<b>User Information:</b>

🆔 <b>User ID:</b> <code>{target_id}</code>
👤 <b>Name:</b> {first_name} {last_name}
🔗 <b>Username:</b> @{username}

━━━━━━━━━━━━━━━━━━━━
<b>📊 STATISTICS:</b>

📅 <b>Joined:</b> {join_date.strftime('%Y-%m-%d %H:%M:%S')}
⏰ <b>Last Active:</b> {last_active.strftime('%Y-%m-%d %H:%M:%S')}
📁 <b>Files Uploaded:</b> {file_count}
⭐ <b>Favorites:</b> {fav_count}
💎 <b>Premium:</b> {'Yes ✨' if is_premium else 'No 🆓'}
🚫 <b>Banned:</b> {'Yes 🔴' if is_banned else 'No 🟢'}
"""
            
            buttons = []
            if not is_banned:
                buttons.append([InlineKeyboardButton(text="🚫 Ban User", callback_data=f"admin_ban_user_id:{target_id}")])
            else:
                buttons.append([InlineKeyboardButton(text="✅ Unban User", callback_data=f"admin_unban_user_id:{target_id}")])
            
            buttons.append([
                InlineKeyboardButton(text="📁 View Files", callback_data=f"admin_view_user_files:{target_id}"),
                InlineKeyboardButton(text="🔙 Back", callback_data="admin_running_scripts")
            ])
        
        back_keyboard = InlineKeyboardMarkup(inline_keyboard=buttons)
        await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
        
    except Exception as e:
        logger.error(f"Error viewing user: {e}", exc_info=True)
        await callback.answer("❌ Error getting user details")

@dp.callback_query(F.data.startswith("admin_view_user_files:"))
async def callback_admin_view_user_files(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    target_id = int(callback.data.split(":", 1)[1])
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    files = user_files.get(target_id, [])
    
    if not files:
        text = f"""
📭 <b>No files found for user {target_id}</b>

This user hasn't uploaded any files yet.
"""
        buttons = []
    else:
        text = f"""
📁 <b>Files for user {target_id}:</b>

"""
        buttons = []
        for i, (file_name, file_type) in enumerate(files, 1):
            text += f"{i}. <code>{file_name}</code> ({file_type})\n"
            buttons.append([
                InlineKeyboardButton(text=f"📥 {file_name[:15]}", callback_data=f"admin_download_file:{target_id}:{file_name}"),
                InlineKeyboardButton(text=f"🗑️ Delete", callback_data=f"admin_delete_file:{target_id}:{file_name}")
            ])
    
    buttons.append([
        InlineKeyboardButton(text="🔙 Back to User", callback_data=f"admin_view_user:{target_id}"),
        InlineKeyboardButton(text="🔙 Admin Panel", callback_data="admin_panel")
    ])
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=buttons)
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data.startswith("admin_download_file:"))
async def callback_admin_download_file(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    _, target_id, file_name = callback.data.split(":", 2)
    target_id = int(target_id)
    
    file_path = UPLOAD_BOTS_DIR / str(target_id) / file_name
    
    if not file_path.exists():
        await callback.answer("❌ File not found!")
        return
    
    # Validate file path
    if not validate_file_path(file_path, target_id):
        await callback.answer("❌ Invalid file path!")
        return
    
    try:
        await callback.message.answer_document(
            document=FSInputFile(file_path),
            caption=f"📥 <b>Admin Download</b>\n👤 User ID: <code>{target_id}</code>\n📁 File: <code>{file_name}</code>",
            parse_mode="HTML"
        )
        await callback.answer()
        
    except Exception as e:
        logger.error(f"Error sending file: {e}", exc_info=True)
        await callback.answer("❌ Error downloading file")

@dp.callback_query(F.data.startswith("admin_delete_file:"))
async def callback_admin_delete_file(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    _, target_id, file_name = callback.data.split(":", 2)
    target_id = int(target_id)
    
    try:
        file_path = UPLOAD_BOTS_DIR / str(target_id) / file_name
        if file_path.exists():
            # Validate path before deletion
            if validate_file_path(file_path, target_id):
                file_path.unlink()
        
        await delete_user_file(target_id, file_name)
        
        await callback.answer(f"✅ File '{file_name}' deleted for user {target_id}")
        await callback_admin_view_user_files(callback)
        
    except Exception as e:
        logger.error(f"Error deleting file: {e}", exc_info=True)
        await callback.answer("❌ Error deleting file")

@dp.callback_query(F.data == "admin_premium_users")
async def callback_admin_premium_users(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    try:
        result = await execute_db_query('SELECT user_id, expiry FROM subscriptions ORDER BY expiry DESC', fetch_all=True)
        premium_users = [(row['user_id'], row['expiry']) for row in result]
        
        if not premium_users:
            text = """
╔═══════════════════════╗
    💎 <b>PREMIUM USERS</b> 💎
╚═══════════════════════╝

📭 <b>No premium users found.</b>

No users have subscribed to premium yet.
"""
            buttons = []
        else:
            text = f"""
╔═══════════════════════╗
    💎 <b>PREMIUM USERS ({len(premium_users)})</b> 💎
╚═══════════════════════╝

"""
            buttons = []
            for i, (premium_id, expiry) in enumerate(premium_users, 1):
                try:
                    expiry_dt = datetime.fromisoformat(expiry)
                    days_left = (expiry_dt - datetime.now()).days
                    expiry_str = expiry_dt.strftime('%Y-%m-%d')
                except:
                    expiry_str = "Invalid date"
                    days_left = "N/A"
                
                text += f"{i}. 👤 <code>{premium_id}</code> | 📅 {expiry_str} | ⏰ {days_left} days left\n"
                
                buttons.append([
                    InlineKeyboardButton(text=f"👁️ View {premium_id}", callback_data=f"admin_view_user:{premium_id}"),
                    InlineKeyboardButton(text=f"🗑️ Remove", callback_data=f"admin_remove_premium:{premium_id}")
                ])
        
        buttons.append([
            InlineKeyboardButton(text="➕ Add Premium", callback_data="admin_add_premium"),
            InlineKeyboardButton(text="🔄 Refresh", callback_data="admin_premium_users")
        ])
        buttons.append([InlineKeyboardButton(text="🔙 Back", callback_data="admin_panel")])
        
        back_keyboard = InlineKeyboardMarkup(inline_keyboard=buttons)
        await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
        
    except Exception as e:
        logger.error(f"Error getting premium users: {e}", exc_info=True)
        await callback.answer("❌ Error getting premium users")

@dp.callback_query(F.data == "admin_add_admin")
async def callback_admin_add_admin(callback: types.CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    text = """
╔═══════════════════════╗
    ➕ <b>ADD ADMIN</b> ➕
╚═══════════════════════╝

<b>Send me the user ID to make admin.</b>

You can get user ID by:
1. Forwarding their message to @userinfobot
2. Asking them to send /start to this bot
3. From user details in admin panel

━━━━━━━━━━━━━━━━━━━━
<b>⚠️ WARNING:</b>

Admins have full control over the bot!
Only add trusted users.
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="❌ Cancel", callback_data="admin_panel")]
    ])
    
    await state.set_state(UploadStates.waiting_for_admin_id)
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.message(UploadStates.waiting_for_admin_id)
async def handle_admin_add(message: types.Message, state: FSMContext):
    user_id = message.from_user.id
    
    if user_id not in admin_ids:
        await message.answer("❌ Admin access required!")
        await state.clear()
        return
    
    try:
        new_admin_id = int(message.text.strip())
        
        if not validate_telegram_id(new_admin_id):
            await message.answer("❌ Invalid Telegram ID format!")
            await state.clear()
            return
        
        if new_admin_id in admin_ids:
            await message.answer(f"❌ User {new_admin_id} is already an admin!")
            await state.clear()
            return
        
        admin_ids.add(new_admin_id)
        
        try:
            await execute_db_query('INSERT OR REPLACE INTO admins (user_id, added_by, added_date) VALUES (?, ?, ?)',
                                 (new_admin_id, user_id, datetime.now().isoformat()))
        except Exception as e:
            logger.error(f"Error saving admin: {e}", exc_info=True)
        
        await message.answer(f"✅ User <code>{new_admin_id}</code> has been added as admin!", parse_mode="HTML")
        
        try:
            await bot.send_message(
                new_admin_id,
                f"🎉 <b>You have been promoted to Admin!</b>\n\n"
                f"Added by: <code>{user_id}</code>\n"
                f"You now have full access to the admin panel.",
                parse_mode="HTML"
            )
        except:
            pass
        
        await state.clear()
        
    except ValueError:
        await message.answer("❌ Invalid user ID! Please send a valid numeric ID.")
    except Exception as e:
        logger.error(f"Error adding admin: {e}", exc_info=True)
        await message.answer("❌ Error adding admin")
        await state.clear()

@dp.callback_query(F.data == "admin_remove_admin")
async def callback_admin_remove_admin(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    if user_id == OWNER_ID:
        current_admins = [uid for uid in admin_ids if uid != OWNER_ID]
    else:
        current_admins = [uid for uid in admin_ids if uid not in [OWNER_ID, user_id]]
    
    if not current_admins:
        text = """
╔═══════════════════════╗
    ➖ <b>REMOVE ADMIN</b> ➖
╚═══════════════════════╝

📭 <b>No other admins to remove.</b>

Only you and the owner are admins.
"""
        buttons = []
    else:
        text = f"""
╔═══════════════════════╗
    ➖ <b>REMOVE ADMIN ({len(current_admins)})</b> ➖
╚═══════════════════════╝

<b>Select admin to remove:</b>

"""
        buttons = []
        for i, admin_id in enumerate(current_admins, 1):
            text += f"{i}. 👤 <code>{admin_id}</code>\n"
            buttons.append([InlineKeyboardButton(text=f"❌ Remove {admin_id}", callback_data=f"remove_admin_confirm:{admin_id}")])
    
    buttons.append([InlineKeyboardButton(text="🔙 Back", callback_data="admin_panel")])
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=buttons)
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data.startswith("remove_admin_confirm:"))
async def callback_remove_admin_confirm(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    target_id = int(callback.data.split(":", 1)[1])
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    if target_id == OWNER_ID:
        await callback.answer("❌ Cannot remove the owner!", show_alert=True)
        return
    
    if user_id != OWNER_ID and target_id == ADMIN_ID:
        await callback.answer("❌ Only owner can remove main admin!", show_alert=True)
        return
    
    text = f"""
⚠️ <b>CONFIRM ADMIN REMOVAL</b> ⚠️

Are you sure you want to remove admin privileges from user <code>{target_id}</code>?

This action cannot be undone!
"""
    
    buttons = [
        [InlineKeyboardButton(text="✅ Yes, Remove", callback_data=f"remove_admin_execute:{target_id}")],
        [InlineKeyboardButton(text="❌ Cancel", callback_data="admin_remove_admin")]
    ]
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=buttons)
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data.startswith("remove_admin_execute:"))
async def callback_remove_admin_execute(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    target_id = int(callback.data.split(":", 1)[1])
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    try:
        admin_ids.discard(target_id)
        
        await execute_db_query('DELETE FROM admins WHERE user_id = ?', (target_id,))
        
        await callback.answer(f"✅ Admin {target_id} removed successfully!")
        
        try:
            await bot.send_message(
                target_id,
                f"📢 <b>Your admin privileges have been removed.</b>\n\n"
                f"Removed by: <code>{user_id}</code>\n"
                f"You no longer have access to admin features.",
                parse_mode="HTML"
            )
        except:
            pass
        
        await callback_admin_remove_admin(callback)
        
    except Exception as e:
        logger.error(f"Error removing admin: {e}", exc_info=True)
        await callback.answer("❌ Error removing admin")

@dp.callback_query(F.data == "admin_ban_user")
async def callback_admin_ban_user(callback: types.CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    text = """
╔═══════════════════════╗
    🚫 <b>BAN USER</b> 🚫
╚═══════════════════════╝

<b>Send me the user ID to ban.</b>

You can get user ID by:
1. Forwarding their message to @userinfobot
2. From user details in admin panel
3. Asking them to send /start

━━━━━━━━━━━━━━━━━━━━
<b>⚠️ WARNING:</b>

Banned users cannot use the bot!
They will see a ban message on /start.
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="❌ Cancel", callback_data="admin_panel")]
    ])
    
    await state.set_state(UploadStates.waiting_for_ban_user)
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.message(UploadStates.waiting_for_ban_user)
async def handle_ban_user(message: types.Message, state: FSMContext):
    user_id = message.from_user.id
    
    if user_id not in admin_ids:
        await message.answer("❌ Admin access required!")
        await state.clear()
        return
    
    try:
        ban_id = int(message.text.strip())
        
        if not validate_telegram_id(ban_id):
            await message.answer("❌ Invalid Telegram ID format!")
            await state.clear()
            return
        
        if ban_id in admin_ids:
            await message.answer("❌ Cannot ban an admin!")
            await state.clear()
            return
        
        if ban_id == OWNER_ID:
            await message.answer("❌ Cannot ban the owner!")
            await state.clear()
            return
        
        banned_users.add(ban_id)
        
        try:
            await execute_db_query('INSERT OR REPLACE INTO banned_users (user_id, banned_date, reason, banned_by) VALUES (?, ?, ?, ?)',
                                 (ban_id, datetime.now().isoformat(), "Banned by admin", user_id))
        except Exception as e:
            logger.error(f"Error saving ban: {e}", exc_info=True)
        
        await message.answer(f"✅ User <code>{ban_id}</code> has been banned!", parse_mode="HTML")
        
        try:
            await bot.send_message(
                ban_id,
                f"🚫 <b>You have been banned from using this bot!</b>\n\n"
                f"Banned by: <code>{user_id}</code>\n"
                f"Reason: Banned by admin\n\n"
                f"Contact admin if you think this is a mistake.",
                parse_mode="HTML"
            )
        except:
            pass
        
        await state.clear()
        
    except ValueError:
        await message.answer("❌ Invalid user ID! Please send a valid numeric ID.")
    except Exception as e:
        logger.error(f"Error banning user: {e}", exc_info=True)
        await message.answer("❌ Error banning user")
        await state.clear()

@dp.callback_query(F.data == "admin_unban_user")
async def callback_admin_unban_user(callback: types.CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    text = """
╔═══════════════════════╗
    ✅ <b>UNBAN USER</b> ✅
╚═══════════════════════╝

<b>Send me the user ID to unban.</b>

Enter the ID of the user you want to unban.
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="❌ Cancel", callback_data="admin_panel")]
    ])
    
    await state.set_state(UploadStates.waiting_for_unban_user)
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.message(UploadStates.waiting_for_unban_user)
async def handle_unban_user(message: types.Message, state: FSMContext):
    user_id = message.from_user.id
    
    if user_id not in admin_ids:
        await message.answer("❌ Admin access required!")
        await state.clear()
        return
    
    try:
        unban_id = int(message.text.strip())
        
        if not validate_telegram_id(unban_id):
            await message.answer("❌ Invalid Telegram ID format!")
            await state.clear()
            return
        
        if unban_id not in banned_users:
            await message.answer(f"❌ User {unban_id} is not banned!")
            await state.clear()
            return
        
        banned_users.discard(unban_id)
        
        try:
            await execute_db_query('DELETE FROM banned_users WHERE user_id = ?', (unban_id,))
        except Exception as e:
            logger.error(f"Error removing ban: {e}", exc_info=True)
        
        await message.answer(f"✅ User <code>{unban_id}</code> has been unbanned!", parse_mode="HTML")
        
        try:
            await bot.send_message(
                unban_id,
                f"✅ <b>Your ban has been lifted!</b>\n\n"
                f"Unbanned by: <code>{user_id}</code>\n"
                f"You can now use the bot again.\n\n"
                f"Send /start to begin.",
                parse_mode="HTML"
            )
        except:
            pass
        
        await state.clear()
        
    except ValueError:
        await message.answer("❌ Invalid user ID! Please send a valid numeric ID.")
    except Exception as e:
        logger.error(f"Error unbanning user: {e}", exc_info=True)
        await message.answer("❌ Error unbanning user")
        await state.clear()

@dp.callback_query(F.data.startswith("admin_ban_user_id:"))
async def callback_admin_ban_user_id(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    target_id = int(callback.data.split(":", 1)[1])
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    if target_id in admin_ids:
        await callback.answer("❌ Cannot ban an admin!")
        return
    
    if target_id == OWNER_ID:
        await callback.answer("❌ Cannot ban the owner!")
        return
    
    banned_users.add(target_id)
    
    try:
        await execute_db_query('INSERT OR REPLACE INTO banned_users (user_id, banned_date, reason, banned_by) VALUES (?, ?, ?, ?)',
                             (target_id, datetime.now().isoformat(), "Banned from admin panel", user_id))
    except Exception as e:
        logger.error(f"Error saving ban: {e}", exc_info=True)
    
    await callback.answer(f"✅ User {target_id} banned!")
    await callback_admin_view_user(callback)

@dp.callback_query(F.data.startswith("admin_unban_user_id:"))
async def callback_admin_unban_user_id(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    target_id = int(callback.data.split(":", 1)[1])
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    banned_users.discard(target_id)
    
    try:
        await execute_db_query('DELETE FROM banned_users WHERE user_id = ?', (target_id,))
    except Exception as e:
        logger.error(f"Error removing ban: {e}", exc_info=True)
    
    await callback.answer(f"✅ User {target_id} unbanned!")
    await callback_admin_view_user(callback)

@dp.callback_query(F.data == "admin_analytics")
async def callback_admin_analytics(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    try:
        # Get stats
        result = await execute_db_query('SELECT stat_name, stat_value FROM bot_stats', fetch_all=True)
        stats = {row['stat_name']: row['stat_value'] for row in result}
        
        # Get user count
        user_result = await execute_db_query('SELECT COUNT(*) as count FROM active_users', fetch_one=True)
        total_users = user_result['count']
        
        # Get file count
        file_result = await execute_db_query('SELECT COUNT(*) as count FROM user_files', fetch_one=True)
        total_files = file_result['count']
        
        # Get running scripts count
        script_result = await execute_db_query('SELECT COUNT(*) as count FROM running_scripts', fetch_one=True)
        running_scripts = script_result['count']
        
        text = f"""
╔═══════════════════════╗
    📊 <b>BOT ANALYTICS</b> 📊
╚═══════════════════════╝

<b>📈 OVERALL STATISTICS:</b>

👥 <b>Total Users:</b> {total_users}
📁 <b>Total Files:</b> {total_files}
🚀 <b>Running Scripts:</b> {running_scripts}
📤 <b>Total Uploads:</b> {stats.get('total_uploads', 0)}
📥 <b>Total Downloads:</b> {stats.get('total_downloads', 0)}
▶️ <b>Total Script Runs:</b> {stats.get('total_runs', 0)}

━━━━━━━━━━━━━━━━━━━━
<b>📊 PERFORMANCE METRICS:</b>

📈 <b>Upload Rate:</b> {stats.get('total_uploads', 0)/max(total_users, 1):.1f} per user
📉 <b>Download Rate:</b> {(stats.get('total_downloads', 0)/max(stats.get('total_uploads', 1), 1)*100):.1f}%
🎯 <b>Activity Rate:</b> {(running_scripts/max(total_users, 1)*100) if total_users > 0 else 0:.1f}%

━━━━━━━━━━━━━━━━━━━━
<b>📅 DAILY AVERAGES:</b>

• Uploads per day: {stats.get('total_uploads', 0)/30:.1f}
• Downloads per day: {stats.get('total_downloads', 0)/30:.1f}
• Scripts per day: {stats.get('total_runs', 0)/30:.1f}
• New users per day: {total_users/30:.1f}
"""
        
        back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
            [InlineKeyboardButton(text="🔄 Refresh", callback_data="admin_analytics")],
            [InlineKeyboardButton(text="🔙 Back", callback_data="admin_panel")]
        ])
        
        await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
        
    except Exception as e:
        logger.error(f"Error getting analytics: {e}", exc_info=True)
        await callback.answer("❌ Error getting analytics")

@dp.callback_query(F.data == "admin_system_status")
async def callback_admin_system_status(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    cpu_percent = psutil.cpu_percent(interval=1)
    memory = psutil.virtual_memory()
    disk = psutil.disk_usage('/')
    boot_time = datetime.fromtimestamp(psutil.boot_time())
    uptime = datetime.now() - boot_time
    
    try:
        net_io = psutil.net_io_counters()
        network_stats = f"📤 Sent: {net_io.bytes_sent / 1024 / 1024:.1f} MB | 📥 Recv: {net_io.bytes_recv / 1024 / 1024:.1f} MB"
    except:
        network_stats = "Network stats unavailable"
    
    text = f"""
╔═══════════════════════╗
    ⚙️ <b>SYSTEM STATUS</b> ⚙️
╚═══════════════════════╝

<b>🖥️ HARDWARE USAGE:</b>

⚡ <b>CPU Usage:</b> {cpu_percent}%
🧠 <b>Memory Usage:</b> {memory.percent}% ({memory.used / 1024 / 1024:.0f}MB / {memory.total / 1024 / 1024:.0f}MB)
💾 <b>Disk Usage:</b> {disk.percent}% ({disk.used / 1024 / 1024 / 1024:.1f}GB / {disk.total / 1024 / 1024 / 1024:.1f}GB)

━━━━━━━━━━━━━━━━━━━━
<b>🌐 NETWORK:</b>

{network_stats}

━━━━━━━━━━━━━━━━━━━━
<b>⏰ SYSTEM UPTIME:</b>

🕒 <b>Boot Time:</b> {boot_time.strftime('%Y-%m-%d %H:%M:%S')}
⏳ <b>Uptime:</b> {uptime.days} days, {uptime.seconds // 3600} hours

━━━━━━━━━━━━━━━━━━━━
<b>🤖 BOT STATUS:</b>

🔒 <b>Bot Lock:</b> {'Enabled 🔴' if bot_locked else 'Disabled 🟢'}
👥 <b>Active Users:</b> {len(active_users)}
📁 <b>User Files:</b> {sum(len(files) for files in user_files.values())}
🚀 <b>Running Processes:</b> {sum(len(scripts) for scripts in bot_scripts.values())}
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔄 Refresh", callback_data="admin_system_status")],
        [InlineKeyboardButton(text="🔙 Back", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "lock_bot")
async def callback_lock_bot(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    global bot_locked
    
    if bot_locked:
        bot_locked = False
        status = "🔓 Bot unlocked"
        message_text = "✅ Bot is now unlocked and accessible to all users."
    else:
        bot_locked = True
        status = "🔒 Bot locked"
        message_text = "🚫 Bot is now locked. Only admins can use it."
    
    await callback.answer(status)
    
    text = f"""
╔═══════════════════════╗
    🔒 <b>BOT LOCK STATUS</b> 🔒
╚═══════════════════════╝

{message_text}

<b>Current Status:</b> {'Locked 🔴' if bot_locked else 'Unlocked 🟢'}
<b>Changed by:</b> <code>{user_id}</code>
<b>Time:</b> {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}

━━━━━━━━━━━━━━━━━━━━
<b>⚠️ NOTE:</b>

When locked, only admins can use the bot.
Regular users will see a maintenance message.
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="🔄 Toggle Again", callback_data="lock_bot")],
        [InlineKeyboardButton(text="🔙 Back", callback_data="admin_panel")]
    ])
    
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")

@dp.callback_query(F.data == "broadcast")
async def callback_broadcast(callback: types.CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    text = """
╔═══════════════════════╗
    📢 <b>BROADCAST MESSAGE</b> 📢
╚═══════════════════════╝

<b>Send me the message to broadcast to all users.</b>

━━━━━━━━━━━━━━━━━━━━
<b>💡 TIPS:</b>

• You can use HTML formatting
• Add links with <a href="url">text</a>
• Max length: 4000 characters
• Use /cancel to abort

━━━━━━━━━━━━━━━━━━━━
<b>⚠️ WARNING:</b>

This will send to ALL users!
Use carefully.
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="❌ Cancel", callback_data="admin_panel")]
    ])
    
    await state.set_state(UploadStates.waiting_for_broadcast)
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.message(UploadStates.waiting_for_broadcast)
async def handle_broadcast(message: types.Message, state: FSMContext):
    user_id = message.from_user.id
    
    if user_id not in admin_ids:
        await message.answer("❌ Admin access required!")
        await state.clear()
        return
    
    broadcast_text = message.text or message.caption
    
    if not broadcast_text:
        await message.answer("❌ Please send text message to broadcast!")
        return
    
    if message.text == "/cancel":
        await message.answer("❌ Broadcast cancelled.")
        await state.clear()
        return
    
    # Check message length
    if len(broadcast_text) > Config.BROADCAST_MESSAGE_LIMIT:
        await message.answer(f"❌ Message too long! Maximum {Config.BROADCAST_MESSAGE_LIMIT} characters.")
        await state.clear()
        return
    
    try:
        all_users = []
        offset = 0
        batch_size = 1000
        
        while True:
            result = await execute_db_query('SELECT user_id FROM active_users LIMIT ? OFFSET ?', 
                                          (batch_size, offset), fetch_all=True)
            if not result:
                break
            
            all_users.extend([row['user_id'] for row in result])
            offset += batch_size
        
        total_users = len(all_users)
        success = 0
        failed = 0
        
        await message.answer(f"📤 Starting broadcast to {total_users} users...")
        
        for i in range(0, total_users, Config.BROADCAST_BATCH_SIZE):
            batch = all_users[i:i + Config.BROADCAST_BATCH_SIZE]
            batch_tasks = []
            
            for user in batch:
                task = bot.send_message(
                    user,
                    f"📢 <b>ANNOUNCEMENT FROM ADMIN</b>\n\n"
                    f"{broadcast_text}\n\n"
                    f"<i>Sent by admin: {message.from_user.full_name}</i>",
                    parse_mode="HTML"
                )
                batch_tasks.append(task)
            
            try:
                results = await asyncio.gather(*batch_tasks, return_exceptions=True)
                for result in results:
                    if isinstance(result, Exception):
                        failed += 1
                    else:
                        success += 1
            except Exception as e:
                logger.error(f"Error in broadcast batch: {e}", exc_info=True)
                failed += len(batch_tasks)
            
            if i + Config.BROADCAST_BATCH_SIZE < total_users:
                await asyncio.sleep(Config.BROADCAST_DELAY)
        
        await message.answer(
            f"✅ <b>BROADCAST COMPLETE!</b>\n\n"
            f"📊 <b>Results:</b>\n"
            f"✅ Success: {success} users\n"
            f"❌ Failed: {failed} users\n"
            f"📈 Success Rate: {success/max(total_users, 1)*100:.1f}%"
        )
        
    except Exception as e:
        logger.error(f"Error in broadcast: {e}", exc_info=True)
        await message.answer(f"❌ Error during broadcast: {str(e)[:200]}")
    
    await state.clear()

@dp.callback_query(F.data == "admin_clean_files")
async def callback_admin_clean_files(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    try:
        cutoff_date = datetime.now() - timedelta(days=Config.CLEANUP_DAYS)
        deleted_files = 0
        deleted_size = 0
        
        for user_dir in UPLOAD_BOTS_DIR.iterdir():
            if user_dir.is_dir():
                for file_path in user_dir.iterdir():
                    if file_path.is_file():
                        file_mtime = datetime.fromtimestamp(file_path.stat().st_mtime)
                        if file_mtime < cutoff_date:
                            try:
                                file_size = file_path.stat().st_size
                                file_path.unlink()
                                deleted_files += 1
                                deleted_size += file_size
                            except:
                                pass
        
        await callback.answer(f"✅ Deleted {deleted_files} old files ({deleted_size/1024/1024:.1f} MB)")
        
        text = f"""
🗑️ <b>CLEANUP COMPLETE</b>

✅ Deleted {deleted_files} files older than {Config.CLEANUP_DAYS} days
💾 Freed {deleted_size/1024/1024:.1f} MB of space

The cleanup was successful!
"""
        
        buttons = [
            [InlineKeyboardButton(text="🔄 Clean More", callback_data="admin_clean_files")],
            [InlineKeyboardButton(text="🔙 Back", callback_data="admin_panel")]
        ]
        
        back_keyboard = InlineKeyboardMarkup(inline_keyboard=buttons)
        await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
        
    except Exception as e:
        logger.error(f"Error cleaning old files: {e}", exc_info=True)
        await callback.answer("❌ Error during cleanup")

@dp.callback_query(F.data == "admin_backup_db")
async def callback_admin_backup_db(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    try:
        # Check disk space
        disk_usage = psutil.disk_usage('/')
        if disk_usage.free < 100 * 1024 * 1024:  # Less than 100MB free
            await callback.answer("❌ Low disk space for backup!", show_alert=True)
            return
        
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        backup_file = BACKUP_DIR / f"backup_{timestamp}.db"
        
        shutil.copy2(DATABASE_PATH, backup_file)
        
        backup_size = backup_file.stat().st_size
        
        if backup_size > 50 * 1024 * 1024:  # Larger than 50MB
            await callback.message.answer("⚠️ Backup file is large (>50MB). Download may take time.")
        
        await callback.message.answer_document(
            document=FSInputFile(backup_file),
            caption=f"💾 <b>Database Backup</b>\n\n"
                   f"📅 Date: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
                   f"💾 Size: {backup_size / 1024:.1f} KB\n"
                   f"👤 Created by: <code>{user_id}</code>",
            parse_mode="HTML"
        )
        
        await callback.answer("✅ Backup created and sent!")
        
    except Exception as e:
        logger.error(f"Error creating backup: {e}", exc_info=True)
        await callback.answer("❌ Error creating backup")

@dp.callback_query(F.data == "admin_view_logs")
async def callback_admin_view_logs(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    log_file = Path('bot.log')
    
    try:
        if not log_file.exists():
            text = "📭 <b>No log file found.</b>\n\nLogging might not be enabled."
        else:
            log_size = log_file.stat().st_size
            
            if log_size > 1024 * 1024:  # 1MB
                text = f"""
📋 <b>LOG FILE TOO LARGE</b>

Log file size: {log_size / 1024 / 1024:.1f} MB

Please download the log file to view it.
"""
                buttons = [
                    [InlineKeyboardButton(text="📥 Download Logs", callback_data="admin_download_logs")],
                    [InlineKeyboardButton(text="🔙 Back", callback_data="admin_panel")]
                ]
            else:
                with open(log_file, 'r', encoding='utf-8') as f:
                    logs = f.read()[-3000:]  # Last 3000 characters
                
                text = f"""
📋 <b>RECENT LOGS</b>

<pre>{logs}</pre>
"""
                buttons = [
                    [InlineKeyboardButton(text="📥 Download Full Logs", callback_data="admin_download_logs")],
                    [InlineKeyboardButton(text="🔄 Refresh", callback_data="admin_view_logs")],
                    [InlineKeyboardButton(text="🔙 Back", callback_data="admin_panel")]
                ]
        
        back_keyboard = InlineKeyboardMarkup(inline_keyboard=buttons)
        await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
        
    except Exception as e:
        logger.error(f"Error viewing logs: {e}", exc_info=True)
        await callback.answer("❌ Error viewing logs")

@dp.callback_query(F.data == "admin_download_logs")
async def callback_admin_download_logs(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    log_file = Path('bot.log')
    
    if not log_file.exists():
        await callback.answer("❌ No log file found!")
        return
    
    try:
        await callback.message.answer_document(
            document=FSInputFile(log_file),
            caption=f"📋 <b>Bot Logs</b>\n\n"
                   f"📅 Generated: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n"
                   f"💾 Size: {log_file.stat().st_size / 1024:.1f} KB\n"
                   f"👤 Requested by: <code>{user_id}</code>",
            parse_mode="HTML"
        )
        await callback.answer()
    except Exception as e:
        logger.error(f"Error sending logs: {e}", exc_info=True)
        await callback.answer("❌ Error sending logs")

@dp.callback_query(F.data.startswith("admin_remove_premium:"))
async def callback_admin_remove_premium(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    target_id = int(callback.data.split(":", 1)[1])
    
    try:
        if target_id in user_subscriptions:
            del user_subscriptions[target_id]
        
        await execute_db_query('DELETE FROM subscriptions WHERE user_id = ?', (target_id,))
        
        await callback.answer(f"✅ Premium removed from user {target_id}")
        
        try:
            await bot.send_message(
                target_id,
                f"📢 <b>Your premium subscription has been removed.</b>\n\n"
                f"Removed by: <code>{user_id}</code>\n"
                f"You are now on the free plan.",
                parse_mode="HTML"
            )
        except:
            pass
        
        # Refresh the premium users list
        await callback_admin_premium_users(callback)
        
    except Exception as e:
        logger.error(f"Error removing premium: {e}", exc_info=True)
        await callback.answer("❌ Error removing premium")

@dp.callback_query(F.data == "admin_add_premium")
async def callback_admin_add_premium(callback: types.CallbackQuery, state: FSMContext):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    text = """
╔═══════════════════════╗
    💎 <b>ADD PREMIUM</b> 💎
╚═══════════════════════╝

<b>Send me the user ID and days for premium.</b>

Format: <code>user_id days</code>

Example: <code>123456789 30</code> (30 days premium)

━━━━━━━━━━━━━━━━━━━━
<b>⚠️ NOTE:</b>

• Max days: 365
• Premium starts immediately
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="❌ Cancel", callback_data="admin_premium_users")]
    ])
    
    await state.set_state(UploadStates.waiting_for_premium)
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.message(UploadStates.waiting_for_premium)
async def handle_add_premium(message: types.Message, state: FSMContext):
    user_id = message.from_user.id
    
    if user_id not in admin_ids:
        await message.answer("❌ Admin access required!")
        await state.clear()
        return
    
    try:
        parts = message.text.strip().split()
        if len(parts) != 2:
            await message.answer("❌ Invalid format! Use: <code>user_id days</code>")
            return
        
        target_id = int(parts[0])
        days = int(parts[1])
        
        if not validate_telegram_id(target_id):
            await message.answer("❌ Invalid Telegram ID format!")
            await state.clear()
            return
        
        if days < 1 or days > 365:
            await message.answer("❌ Days must be between 1 and 365!")
            return
        
        expiry_date = datetime.now() + timedelta(days=days)
        user_subscriptions[target_id] = {'expiry': expiry_date}
        
        await execute_db_query('INSERT OR REPLACE INTO subscriptions (user_id, expiry) VALUES (?, ?)',
                             (target_id, expiry_date.isoformat()))
        
        await message.answer(f"✅ Premium added for user {target_id} for {days} days!")
        
        try:
            await bot.send_message(
                target_id,
                f"🎉 <b>You have been granted premium access!</b>\n\n"
                f"Duration: {days} days\n"
                f"Expires: {expiry_date.strftime('%Y-%m-%d')}\n"
                f"Granted by: <code>{user_id}</code>\n\n"
                f"Your upload limit is now {Config.SUBSCRIBED_USER_LIMIT} files!",
                parse_mode="HTML"
            )
        except:
            pass
        
        await state.clear()
        
    except ValueError:
        await message.answer("❌ Invalid input! Use: <code>user_id days</code>")
    except Exception as e:
        logger.error(f"Error adding premium: {e}", exc_info=True)
        await message.answer("❌ Error adding premium")
        await state.clear()

@dp.callback_query(F.data == "admin_restart_bot")
async def callback_admin_restart_bot(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    text = """
⚠️ <b>CONFIRM BOT RESTART</b> ⚠️

Are you sure you want to restart the bot?

This will:
1. Stop all running scripts
2. Save current state
3. Restart the bot process
4. Reconnect to Telegram

━━━━━━━━━━━━━━━━━━━━
<b>⚠️ WARNING:</b>

• Users might experience temporary disconnection
• Running scripts will be terminated
• Bot will be offline for a few seconds
"""
    
    buttons = [
        [InlineKeyboardButton(text="✅ Yes, Restart", callback_data="restart_bot_confirm")],
        [InlineKeyboardButton(text="❌ Cancel", callback_data="admin_panel")]
    ]
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=buttons)
    await callback.message.edit_text(text, reply_markup=back_keyboard, parse_mode="HTML")
    await callback.answer()

@dp.callback_query(F.data == "restart_bot_confirm")
async def callback_restart_bot_confirm(callback: types.CallbackQuery):
    user_id = callback.from_user.id
    
    if user_id not in admin_ids:
        await callback.answer("❌ Admin access required!", show_alert=True)
        return
    
    await callback.answer("🔄 Restarting bot...")
    
    try:
        # Stop all running scripts
        for uid, scripts in bot_scripts.items():
            for fname, pid in scripts.items():
                try:
                    process = psutil.Process(pid)
                    process.terminate()
                except:
                    pass
        
        # Save stats
        for stat_name, stat_value in bot_stats.items():
            await execute_db_query('UPDATE bot_stats SET stat_value = ? WHERE stat_name = ?', (stat_value, stat_name))
        
        await callback.message.answer("✅ Bot restart initiated...")
        
        # Restart
        python = sys.executable
        os.execl(python, python, *sys.argv)
        
    except Exception as e:
        logger.error(f"Error restarting bot: {e}", exc_info=True)
        await callback.message.answer(f"❌ Error restarting: {str(e)}")

@dp.message(Command("help"))
async def cmd_help(message: types.Message):
    """Show help information."""
    user_id = message.from_user.id
    
    if check_bot_locked(user_id):
        await message.answer("🔒 Bot is locked for maintenance!")
        return
    
    text = """
╔═══════════════════════╗
    ℹ️ <b>HELP & INFORMATION</b> ℹ️
╚═══════════════════════╝

<b>📚 AVAILABLE COMMANDS:</b>

• /start - Start the bot
• /stop <pid> - Stop running script
• /search <query> - Search files
• /stats - Show your statistics
• /help - Show this message

━━━━━━━━━━━━━━━━━━━━
<b>🎯 BOT FEATURES:</b>

• 📤 Upload files (.py, .js, .zip)
• 📁 Manage your files
• ⭐ Mark files as favorites
• 🔍 Search through files
• ▶️ Run Python/JS scripts
• 🛑 Stop running scripts
• 📥 Download your files
• 📊 View statistics
• ⚡ Speed test

━━━━━━━━━━━━━━━━━━━━
<b>⚠️ IMPORTANT NOTES:</b>

1. Max file size: 50MB
2. Supported: Python, JavaScript, ZIP
3. Scripts run with timeout
4. Keep backups of your files
5. Contact admin for issues

━━━━━━━━━━━━━━━━━━━━
<b>👥 SUPPORT:</b>

For help, contact: @DarkConflig
Join updates: @DarkConflig_Updates
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📢 Updates Channel", url=UPDATE_CHANNEL)],
        [InlineKeyboardButton(text="💬 Contact Owner", url=f"https://t.me/{YOUR_USERNAME.replace('@', '')}")],
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    
    await message.answer(text, reply_markup=back_keyboard, parse_mode="HTML")

@dp.message(Command("stats"))
async def cmd_stats(message: types.Message):
    """Show user statistics."""
    user_id = message.from_user.id
    
    if check_bot_locked(user_id):
        await message.answer("🔒 Bot is locked for maintenance!")
        return
    
    files = user_files.get(user_id, [])
    
    py_count = sum(1 for f in files if f[1] == 'py')
    js_count = sum(1 for f in files if f[1] == 'js')
    zip_count = sum(1 for f in files if f[1] == 'zip')
    
    total_size = 0
    user_dir = UPLOAD_BOTS_DIR / str(user_id)
    if user_dir.exists():
        for file in user_dir.iterdir():
            if file.is_file():
                total_size += file.stat().st_size
    
    text = f"""
╔═══════════════════════╗
    📊 <b>YOUR STATISTICS</b> 📊
╚═══════════════════════╝

👤 <b>User:</b> {message.from_user.full_name}
🆔 <b>ID:</b> <code>{user_id}</code>
💎 <b>Status:</b> {'Premium ✨' if user_id in user_subscriptions else 'Free 🆓'}

━━━━━━━━━━━━━━━━━━━━
<b>📁 FILE STATS:</b>

📦 <b>Total Files:</b> {len(files)}
🐍 <b>Python Files:</b> {py_count}
🟨 <b>JavaScript Files:</b> {js_count}
📦 <b>ZIP Archives:</b> {zip_count}
💾 <b>Total Size:</b> {total_size / 1024 / 1024:.2f} MB

━━━━━━━━━━━━━━━━━━━━
<b>⭐ FAVORITES:</b>
❤️ <b>Favorite Files:</b> {len(user_favorites.get(user_id, []))}

━━━━━━━━━━━━━━━━━━━━
<b>🎯 ACCOUNT LIMITS:</b>
📤 <b>Upload Limit:</b> {get_user_file_limit(user_id)} files
📥 <b>Current Usage:</b> {len(files)} files
📈 <b>Available:</b> {get_user_file_limit(user_id) - len(files)} files
"""
    
    back_keyboard = InlineKeyboardMarkup(inline_keyboard=[
        [InlineKeyboardButton(text="📁 My Files", callback_data="check_files")],
        [InlineKeyboardButton(text="🏠 Main Menu", callback_data="back_to_main")]
    ])
    
    await message.answer(text, reply_markup=back_keyboard, parse_mode="HTML")

@dp.message(Command("search"))
async def cmd_search(message: types.Message, state: FSMContext):
    """Handle search command."""
    user_id = message.from_user.id
    
    if check_bot_locked(user_id):
        await message.answer("🔒 Bot is locked for maintenance!")
        return
    
    if len(message.text.split()) < 2:
        await message.answer("Usage: /search <query>")
        return
    
    query = ' '.join(message.text.split()[1:])
    await state.set_state(UploadStates.waiting_for_search)
    
    # Create a modified message with just the query
    search_message = types.Message(
        message_id=message.message_id,
        date=message.date,
        chat=message.chat,
        text=query,
        from_user=message.from_user
    )
    
    # Call search handler
    await handle_search_query(search_message, state)

@dp.message()
async def handle_other_messages(message: types.Message):
    user_id = message.from_user.id
    
    if user_id in banned_users:
        return
    
    if check_bot_locked(user_id):
        await message.answer("🔒 Bot is locked for maintenance!")
        return
    
    if message.text and message.text.startswith('/'):
        await message.answer("❌ Unknown command. Use /help to see available commands.")
    else:
        await message.answer("🤖 <b>File Host Bot</b>\n\nUse /start to begin or /help for assistance.", parse_mode="HTML")

async def save_stats_periodically():
    """Periodically save bot stats to database."""
    while True:
        try:
            for stat_name, stat_value in bot_stats.items():
                await execute_db_query('UPDATE bot_stats SET stat_value = ? WHERE stat_name = ?', (stat_value, stat_name))
            logger.info("Statistics saved to database.")
        except Exception as e:
            logger.error(f"Error saving stats: {e}", exc_info=True)
        
        await asyncio.sleep(300)  # Every 5 minutes

async def cleanup_old_data():
    """Periodically clean up old inactive users."""
    while True:
        try:
            cutoff_date = (datetime.now() - timedelta(days=Config.CLEANUP_DAYS * 3)).isoformat()
            await execute_db_query('DELETE FROM active_users WHERE last_active < ?', (cutoff_date,))
            
            logger.info("Periodic cleanup completed.")
        except Exception as e:
            logger.error(f"Error in periodic cleanup: {e}", exc_info=True)
        
        await asyncio.sleep(86400)  # Every 24 hours

async def main():
    """Main bot function."""
    logger.info("Starting bot...")
    
    try:
        # Initialize database
        await init_db()
        await migrate_db()
        await load_data()
        
        # Start periodic tasks
        asyncio.create_task(save_stats_periodically())
        asyncio.create_task(cleanup_old_data())
        
        # Start polling
        logger.info("Bot started successfully!")
        await dp.start_polling(bot)
        
    except KeyboardInterrupt:
        logger.info("Bot stopped by user")
    except Exception as e:
        logger.error(f"Fatal error: {e}", exc_info=True)
        raise

if __name__ == "__main__":
    try:
        asyncio.run(main())
    except KeyboardInterrupt:
        logger.info("Bot stopped")
    except Exception as e:
        logger.error(f"Fatal error: {e}", exc_info=True)
        sys.exit(1)