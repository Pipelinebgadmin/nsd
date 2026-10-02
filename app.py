import os
import json
import re
import uuid
import hashlib
import tempfile
import random
import io
from typing import Any
import secrets
import time
from functools import wraps
from urllib.parse import urlparse
from datetime import datetime, timezone, timedelta
from zoneinfo import ZoneInfo


from flask import Flask, render_template, request, redirect, url_for, flash, session, send_file, jsonify
from werkzeug.security import generate_password_hash, check_password_hash
import hmac

# -------------------------
# Config
# -------------------------
APP_TITLE = "NStock"
# Where all live data (JSON files, secret key) is stored. On Render, point
# NSTOCK_DATA_DIR at a persistent disk (e.g. /var/data) or data is lost on redeploy.
DATA_DIR = os.environ.get("NSTOCK_DATA_DIR") or os.path.join(os.path.dirname(os.path.abspath(__file__)), "data")
DATA_PATH = os.path.join(DATA_DIR, "products.json")

BLENDS_PATH = os.path.join(DATA_DIR, "blends.json")
ALERTS_PATH = os.path.join(DATA_DIR, "alerts.json")
STAGING_PATH = os.path.join(DATA_DIR, "staging.json")
LOCATIONS_PATH = os.path.join(DATA_DIR, "locations.json")
FORMULAS_PATH = os.path.join(DATA_DIR, "formulas.json")
PACKAGES_PATH = os.path.join(DATA_DIR, "packages.json")
PACKAGE_INVENTORY_PATH = os.path.join(DATA_DIR, "package_inventory.json")

# -------------------------
# Tanks (Sublocations) + Tank Ledger (Additive)
# -------------------------
TANKS_PATH = os.path.join(DATA_DIR, "tanks.json")
TANK_LEDGER_PATH = os.path.join(DATA_DIR, "tank_ledger.json")
EVENT_LEDGER_PATH = os.path.join(DATA_DIR, "event_ledger.json")

TANK_CAPACITY_UNIT = "gal"  # capacity is always gallons

PHASES = ("liquid", "solid")
UNITS_LIQUID = ("gal", "lb", "unit")
UNITS_SOLID = ("lb", "unit")  # solids can be lb or unit

app = Flask(__name__)


def _load_secret_key() -> str:
    """
    Session signing key. Uses FLASK_SECRET_KEY if set (do this in production).
    Otherwise generates a random key once and keeps it in data/.secret_key so
    logins survive restarts on the same machine. Never hard-code this.
    """
    env_key = os.environ.get("FLASK_SECRET_KEY")
    if env_key:
        return env_key
    key_path = os.path.join(DATA_DIR, ".secret_key")
    try:
        with open(key_path, "r", encoding="utf-8") as f:
            key = f.read().strip()
            if key:
                return key
    except FileNotFoundError:
        pass
    os.makedirs(DATA_DIR, exist_ok=True)
    key = secrets.token_hex(32)
    with open(key_path, "w", encoding="utf-8") as f:
        f.write(key)
    return key


app.secret_key = _load_secret_key()
app.config.update(
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=os.environ.get("NSTOCK_HTTPS", "0") == "1",
    PERMANENT_SESSION_LIFETIME=timedelta(hours=12),
)


# -------------------------
# CSRF protection
# -------------------------
# Every POST must carry the secret token stored in the user's session. A page on
# another website can't read that token, so it can't submit forms as the user.
# static/js/csrf.js adds the token to every form and fetch() automatically.
CSRF_SESSION_KEY = "csrf_token"
CSRF_METHODS = {"POST", "PUT", "PATCH", "DELETE"}


def csrf_token() -> str:
    token = session.get(CSRF_SESSION_KEY)
    if not token:
        token = secrets.token_urlsafe(32)
        session[CSRF_SESSION_KEY] = token
    return token


app.jinja_env.globals["csrf_token"] = csrf_token


@app.before_request
def csrf_protect():
    if request.method not in CSRF_METHODS or request.endpoint == "static":
        return None
    expected = session.get(CSRF_SESSION_KEY)
    sent = (
        request.form.get("csrf_token")
        or request.headers.get("X-CSRFToken")
        or request.args.get("csrf_token")
        or ""
    )
    if expected and hmac.compare_digest(str(sent), str(expected)):
        return None
    if request.path.startswith("/api/"):
        return jsonify({"error": "Security check failed. Refresh the page and try again."}), 400
    flash("That form expired. Please try again.", "warning")
    back = url_for("home")
    ref = urlparse(request.referrer or "")
    if ref.netloc == request.host and ref.path:
        back = ref.path + (f"?{ref.query}" if ref.query else "")
    return redirect(_safe_next(back))


@app.after_request
def hide_money_in_json(resp):
    try:
        if resp.is_json and request.endpoint not in PUBLIC_ENDPOINTS and current_user() and not can_see_costs():
            data = resp.get_json(silent=True)
            if data is not None:
                resp.set_data(json.dumps(strip_money(data)))
    except Exception:
        pass
    return resp


@app.after_request
def security_headers(resp):
    resp.headers.setdefault("X-Content-Type-Options", "nosniff")
    resp.headers.setdefault("X-Frame-Options", "SAMEORIGIN")  # our own windows use same-site iframes
    resp.headers.setdefault("Referrer-Policy", "same-origin")
    return resp


# -------------------------
# Users + Login
# -------------------------
USERS_PATH = os.path.join(DATA_DIR, "users.json")
ROLES = ("admin", "user")

# Pages anyone can reach without being logged in.
PUBLIC_ENDPOINTS = {"login_page", "setup_page", "static"}

# Simple brute-force protection: after 5 bad passwords, that username is
# locked for 5 minutes. Kept in memory, so it resets if the server restarts.
_FAILED_LOGINS: dict = {}
MAX_FAILED_LOGINS = 5
LOCKOUT_SECONDS = 300


def load_users() -> list:
    return load_json(USERS_PATH, [])


def save_users(users: list) -> None:
    save_json(USERS_PATH, users)


def find_user(username: str):
    key = (username or "").strip().lower()
    for u in load_users():
        if u.get("username", "").lower() == key:
            return u
    return None


def current_user():
    uid = session.get("user_id")
    if not uid:
        return None
    for u in load_users():
        if u.get("id") == uid and u.get("active", True):
            return u
    return None


def _validate_new_password(pw: str, confirm: str):
    if len(pw) < 8:
        return "Password must be at least 8 characters."
    if pw != confirm:
        return "Passwords do not match."
    return None


def _is_locked(username: str) -> bool:
    rec = _FAILED_LOGINS.get(username.lower())
    if not rec:
        return False
    count, first = rec
    if time.time() - first > LOCKOUT_SECONDS:
        _FAILED_LOGINS.pop(username.lower(), None)
        return False
    return count >= MAX_FAILED_LOGINS


def _record_failure(username: str) -> None:
    key = username.lower()
    count, first = _FAILED_LOGINS.get(key, (0, time.time()))
    _FAILED_LOGINS[key] = (count + 1, first)


def _safe_next(target: str) -> str:
    # Only allow redirects back into this app (blocks open-redirect tricks).
    if target and target.startswith("/") and not target.startswith("//"):
        return target
    return url_for("home")


def admin_required(view):
    @wraps(view)
    def wrapper(*args, **kwargs):
        user = current_user()
        if not user or user.get("role") != "admin":
            flash("Admins only.", "danger")
            return redirect(url_for("home"))
        return view(*args, **kwargs)
    return wrapper


@app.before_request
def require_login():
    if request.endpoint in PUBLIC_ENDPOINTS or request.endpoint is None:
        return None
    if not load_users():
        return redirect(url_for("setup_page"))
    if current_user() is None:
        session.pop("user_id", None)
        if request.path.startswith("/api/"):
            return jsonify({"error": "Not logged in"}), 401
        return redirect(url_for("login_page", next=request.full_path.rstrip("?")))
    return None


@app.context_processor
def inject_user():
    return {"current_user": current_user()}


@app.route("/setup", methods=["GET", "POST"])
def setup_page():
    """First run only: create the first admin account."""
    if load_users():
        return redirect(url_for("login_page"))
    error = None
    username = ""
    if request.method == "POST":
        username = request.form.get("username", "").strip()
        pw = request.form.get("password", "")
        error = (None if username else "Username is required.") or \
            _validate_new_password(pw, request.form.get("confirm", ""))
        if not error:
            user = {
                "id": str(uuid.uuid4()),
                "username": username,
                "password_hash": generate_password_hash(pw),
                "role": "admin",
                "active": True,
                "created_at": now_central_iso(),
            }
            save_users([user])
            append_ledger_entry("user_created", {"username": username, "role": "admin", "by": "setup"})
            session.clear()
            session["user_id"] = user["id"]
            session.permanent = True
            return redirect(url_for("home"))
    return render_template("login.html", mode="setup", error=error, username=username)


@app.route("/login", methods=["GET", "POST"])
def login_page():
    if not load_users():
        return redirect(url_for("setup_page"))
    if current_user():
        return redirect(url_for("home"))
    error = None
    username = ""
    next_url = request.values.get("next", "")
    if request.method == "POST":
        username = request.form.get("username", "").strip()
        pw = request.form.get("password", "")
        if _is_locked(username):
            error = "Too many failed attempts. Try again in a few minutes."
        else:
            user = find_user(username)
            if user and user.get("active", True) and check_password_hash(user["password_hash"], pw):
                _FAILED_LOGINS.pop(username.lower(), None)
                session.clear()
                session["user_id"] = user["id"]
                session.permanent = True
                append_ledger_entry("user_login", {"username": user["username"]})
                return redirect(_safe_next(next_url))
            _record_failure(username)
            error = "Incorrect username or password."
    return render_template("login.html", mode="login", error=error, username=username, next_url=next_url)


@app.route("/logout", methods=["POST"])
def logout():
    session.clear()
    return redirect(url_for("login_page"))


# -------------------------
# Permissions
# -------------------------
# Each feature a user can be given. Admins always have every feature.
FEATURES = [
    ("transactions",     "Transaction History",   "View every inventory movement (undo is a separate per-user switch)"),
    ("inventory_view",   "Inventory Overview",    "Inventory overview, live inventory, and search"),
    ("products",         "Products",              "View products and product details"),
    ("products_edit",    "Add & Edit Products",   "Create, edit, and delete products"),
    ("adjust_inventory", "Adjust Inventory",      "Receive, remove, and adjust stock"),
    ("staging",          "Staging",               "Stage and release product"),
    ("blending",         "Blend",                 "Execute blends from saved formulas"),
    ("blend_builder",    "Blend Builder (Quick Build)", "Build a one-off blend without a saved formula"),
    ("formulas",         "Formula Catalog",       "View, create, and edit formulas"),
    ("alerts",           "Reorder Alerts",        "View and manage reorder alerts"),
    ("locations",        "Locations & Tanks",     "View locations and tanks"),
    ("locations_edit",   "Add & Edit Locations",  "Create and edit locations and tanks"),
    ("packages",         "Packages",              "Manage package types"),
    ("spreadsheet",      "Spreadsheet",           "Use the spreadsheet"),
    ("reports",          "Reports",               "View and print reports"),
    ("costs",            "Costs & Values",        "See unit costs, inventory value, cost of goods, and blend/formula costs"),
    ("ledger",           "Event Ledger",          "View the audit ledger (still needs the ledger password)"),
]
FEATURE_KEYS = [f[0] for f in FEATURES]
# New users start with everything except the ledger; the admin adjusts from there.
# Quick Build and the ledger are opt-in: an admin turns them on per user.
# Quick Build, the ledger, and money (Costs & Values) are opt-in: an admin turns them on per user.
DEFAULT_FEATURES = [k for k in FEATURE_KEYS if k not in ("ledger", "blend_builder", "costs")]

# Which feature(s) unlock each page. A user needs ANY one of the listed features.
# Pages shared by several screens (like the inventory API) list every screen that uses them.
ENDPOINT_FEATURES = {
    "dashboard": {"transactions"},
    "transactions_page": {"transactions"},
    "transaction_undo": {"transactions"},
    "inventory_overview": {"inventory_view"},
    "live_inventory_page": {"inventory_view"},
    "product_search": {"inventory_view", "products"},
    "api_location_inventory": {"inventory_view", "adjust_inventory", "blending", "staging", "locations"},
    "list_products": {"products"},
    "product_detail": {"products"},
    "add_product": {"products_edit"},
    "delete_product": {"products_edit"},
    "inventory_adjust_page": {"adjust_inventory"},
    "inventory_add_page": {"adjust_inventory"},
    "inventory_receive_page": {"adjust_inventory"},
    "receive_inventory": {"adjust_inventory"},
    "staging_create_route": {"staging", "adjust_inventory"},
    "staging_release_flow": {"staging", "adjust_inventory"},
    "staging_void_route": {"staging", "adjust_inventory"},
    "staging_page": {"staging"},
    "staging_picked_up": {"staging"},
    "staging_cancel": {"staging"},
    "staging_lift_date": {"staging"},
    "blend_new_page": {"blending", "blend_builder"},
    "blend_builder_info": {"blend_builder"},
    "blend_build": {"blend_builder"},
    "blend_execute_at_location": {"blending", "adjust_inventory"},
    "blend_execute_formula": {"blending"},
    "api_blend_plan": {"blending"},
    "api_blend_validate": {"blending"},
    "blend_log_page": {"blending", "blend_builder"},
    "formulas_page": {"formulas"},
    "formulas_info_page": {"formulas"},
    "formulas_new_page": {"formulas"},
    "formulas_create": {"formulas"},
    "formulas_create_percent": {"formulas"},
    "formulas_update_percent": {"formulas"},
    "formulas_delete": {"formulas"},
    "formulas_save_from_blend": {"formulas"},
    "api_formulas_list": {"formulas", "blending", "blend_builder"},
    "api_formulas_get": {"formulas", "blending", "blend_builder"},
    "api_formula_compute": {"formulas", "blending", "blend_builder"},
    "alerts_page": {"alerts"},
    "alerts_add": {"alerts"},
    "alerts_delete": {"alerts"},
    "locations_page": {"locations"},
    "location_detail_page": {"locations"},
    "location_detail_by_id": {"locations"},
    "tanks_page": {"locations"},
    "add_location": {"locations_edit"},
    "edit_location": {"locations_edit"},
    "add_tank": {"locations_edit"},
    "packages_page": {"packages"},
    "packages_add": {"packages"},
    "packages_edit": {"packages"},
    "packages_delete": {"packages"},
    "api_packages_list": {"packages", "adjust_inventory", "blending"},
    "api_package_inventory": {"packages", "adjust_inventory", "blending"},
    "spreadsheet_page": {"spreadsheet"},
    "spreadsheet_load": {"spreadsheet"},
    "spreadsheet_save": {"spreadsheet"},
    "api_data_context": {"spreadsheet"},
    "api_sheets_list": {"spreadsheet"},
    "api_sheets_create": {"spreadsheet"},
    "api_sheets_rename": {"spreadsheet"},
    "api_sheets_delete": {"spreadsheet"},
    "reports_center": {"reports"},
    "report_inventory_listing": {"reports"},
    "report_inventory_listing_pdf": {"reports"},
    "report_cycle_count": {"reports"},
    "report_cycle_count_pdf": {"reports"},
    "report_blend_instruction": {"reports"},
    "report_blend_instruction_pdf": {"reports"},
    # money reports also need Costs & Values (see COST_ONLY_ENDPOINTS)
    "report_inventory_value": {"reports"},
    "report_inventory_value_pdf": {"reports"},
    "report_avg_cost": {"reports"},
    "report_avg_cost_pdf": {"reports"},
    "report_blend_cost": {"reports"},
    "report_blend_cost_pdf": {"reports"},
    "event_ledger_page": {"ledger"},
    "event_ledger_lock": {"ledger"},
}
# Some pages need a different feature when saving than when viewing.
ENDPOINT_FEATURES_POST = {
    "product_detail": {"products_edit"},
}
# Pages that are entirely about money: need Costs & Values in addition to their normal feature.
COST_ONLY_ENDPOINTS = {
    "report_inventory_value", "report_inventory_value_pdf",
    "report_avg_cost", "report_avg_cost_pdf",
    "report_blend_cost", "report_blend_cost_pdf",
}

# JSON keys that carry money. They're removed from every API response for people
# without Costs & Values, so nothing leaks even if a page tries to show it.
MONEY_KEYS = {
    "unit_cost", "avg_cog", "avg_cost", "avg_unit_cost", "cost", "cost_per_gal", "cost_per_unit",
    "total_cost", "total_cost_value", "inventory_value", "issued_value", "overage_cost",
    "effective_unit_cost", "total_value", "value", "recv_cost", "company_avg_cost", "grand_total",
    "value_at_loc",
}


def strip_money(obj):
    """Copy of obj with every money field removed (recursively)."""
    if isinstance(obj, dict):
        return {k: strip_money(v) for k, v in obj.items() if k not in MONEY_KEYS}
    if isinstance(obj, list):
        return [strip_money(v) for v in obj]
    return obj


def can_see_costs() -> bool:
    return user_can(current_user(), "costs")


# Every logged-in user can reach these.
ALWAYS_ALLOWED = {"index", "home", "logout", "users_page", "user_profile"}
# Only admins, regardless of features.
ADMIN_ONLY = {"admin_page", "admin_sheet_access", "admin_ledger_password", "admin_user_can_undo"}


def normalize_user(u: dict) -> dict:
    """Fill in fields that older accounts don't have yet."""
    u.setdefault("first_name", "")
    u.setdefault("last_name", "")
    u.setdefault("email", "")
    u.setdefault("phone", "")
    u.setdefault("active", True)
    u.setdefault("features", list(DEFAULT_FEATURES))
    # Dashboard was replaced by Transaction History: carry the access over
    if "dashboard" in u["features"]:
        u["features"] = ["transactions" if f == "dashboard" else f for f in u["features"]]
    u.setdefault("locations", "all")
    u.setdefault("can_undo", True)
    return u


def user_display_name(u: dict) -> str:
    full = f"{u.get('first_name', '')} {u.get('last_name', '')}".strip()
    return full or u.get("username", "")


def user_can(user, feature: str) -> bool:
    if not user:
        return False
    if user.get("role") == "admin":
        return True
    return feature in normalize_user(user).get("features", [])


def endpoint_allowed(user, endpoint: str, method: str = "GET") -> bool:
    if user.get("role") == "admin":
        return True
    if endpoint in COST_ONLY_ENDPOINTS and not user_can(user, "costs"):
        return False
    if endpoint in ADMIN_ONLY:
        return False
    if endpoint in ALWAYS_ALLOWED:
        return True
    needed = ENDPOINT_FEATURES_POST.get(endpoint) if method == "POST" else None
    needed = needed or ENDPOINT_FEATURES.get(endpoint)
    if needed is None:
        # Pages not in the list are blocked for non-admins until someone adds them above.
        return False
    return any(user_can(user, f) for f in needed)


@app.before_request
def enforce_permissions():
    if request.endpoint in PUBLIC_ENDPOINTS or request.endpoint is None:
        return None
    user = current_user()
    if user is None:
        return None  # require_login already handled this
    if endpoint_allowed(user, request.endpoint, request.method):
        return None
    if request.path.startswith("/api/"):
        return jsonify({"error": "You don't have access to this."}), 403
    return render_template("no_access.html"), 403


# -------------------------
# Location access
# -------------------------
# Request fields that name a location. If a restricted user sends one of these
# pointing at a location they aren't assigned to, the request is refused.
LOCATION_FIELDS = ("location", "location_id", "from_location_id", "to_location_id")


def allowed_location_ids(user):
    """None means every location. Otherwise a set of location ids."""
    if not user or user.get("role") == "admin":
        return None
    locs = normalize_user(user).get("locations", "all")
    if locs == "all":
        return None
    return set(locs)


def user_can_use_location(user, loc_id=None, loc_name=None) -> bool:
    allowed = allowed_location_ids(user)
    if allowed is None:
        return True
    locations = load_json(LOCATIONS_PATH, [])
    if loc_id is not None:
        loc_id = str(loc_id).strip()
        if any(str(l.get("id")) == loc_id for l in locations):
            return loc_id in allowed
    if loc_name is not None:
        key = str(loc_name).strip().lower()
        match = next((l for l in locations if (l.get("name") or "").strip().lower() == key), None)
        if match:
            return str(match.get("id")) in allowed
    # Not a known location (blank, or free text like "Production"): nothing to block.
    return True


def load_locations_for_user():
    """Locations the current user is assigned to, for lists and dropdowns."""
    locations = load_json(LOCATIONS_PATH, [])
    allowed = allowed_location_ids(current_user())
    if allowed is None:
        return locations
    return [l for l in locations if str(l.get("id")) in allowed]


@app.before_request
def enforce_locations():
    if request.endpoint in PUBLIC_ENDPOINTS or request.endpoint is None:
        return None
    user = current_user()
    if user is None or allowed_location_ids(user) is None:
        return None

    blocked = False
    view_args = request.view_args or {}
    if "location_id" in view_args and not user_can_use_location(user, loc_id=view_args["location_id"]):
        blocked = True
    if "location_name" in view_args and not user_can_use_location(user, loc_name=view_args["location_name"]):
        blocked = True

    sources = [request.args, request.form]
    body = request.get_json(silent=True) if request.is_json else None
    if isinstance(body, dict):
        sources.append(body)
    for src in sources:
        for field in LOCATION_FIELDS:
            val = src.get(field)
            if val and not (user_can_use_location(user, loc_id=val) and user_can_use_location(user, loc_name=val)):
                blocked = True

    if not blocked:
        return None
    if request.path.startswith("/api/"):
        return jsonify({"error": "You don't have access to that location."}), 403
    return render_template("no_access.html", message="You aren't assigned to that location."), 403


@app.context_processor
def inject_permissions():
    user = current_user()
    return {
        "can": lambda feature: (
            any(user_can(user, f) for f in feature) if isinstance(feature, (list, tuple))
            else user_can(user, feature)
        ),
        "user_display_name": user_display_name,
    }


_EMAIL_RE = re.compile(r"^[^@\s]+@[^@\s]+\.[^@\s]+$")


def _clean_profile_form(form, users, editing_id=None):
    """Validate the personal-info fields. Returns (data, error)."""
    data = {
        "first_name": form.get("first_name", "").strip(),
        "last_name": form.get("last_name", "").strip(),
        "username": form.get("username", "").strip(),
        "email": form.get("email", "").strip(),
        "phone": form.get("phone", "").strip(),
    }
    if not data["first_name"] or not data["last_name"]:
        return data, "First and last name are required."
    if not data["username"]:
        return data, "Username is required."
    if " " in data["username"]:
        return data, "Username can't contain spaces."
    for u in users:
        if u.get("id") != editing_id and u.get("username", "").lower() == data["username"].lower():
            return data, "That username is already taken."
    if data["email"] and not _EMAIL_RE.match(data["email"]):
        return data, "That email address doesn't look right."
    if data["phone"]:
        digits = re.sub(r"\D", "", data["phone"])
        if len(digits) < 10 or len(digits) > 15:
            return data, "Phone number should have 10 to 15 digits."
    return data, None


def _active_admin_count(users) -> int:
    return sum(1 for u in users if u.get("role") == "admin" and u.get("active", True))


@app.route("/admin", methods=["GET", "POST"])
@admin_required
def admin_page():
    """User management hub: list everyone, add new users."""
    me = current_user()
    users = [normalize_user(u) for u in load_users()]
    error = None
    form = {}

    if request.method == "POST":
        form = request.form
        data, error = _clean_profile_form(form, users)
        role = form.get("role", "user")
        if not error and role not in ROLES:
            error = "Invalid role."
        if not error:
            error = _validate_new_password(form.get("password", ""), form.get("confirm", ""))
        if not error:
            new_user = normalize_user({
                "id": str(uuid.uuid4()),
                **data,
                "password_hash": generate_password_hash(form["password"]),
                "role": role,
                "active": True,
                "created_at": now_central_iso(),
            })
            users.append(new_user)
            save_users(users)
            append_ledger_entry("user_created", {"username": new_user["username"], "role": role, "by": me["username"]})
            flash(f"{user_display_name(new_user)} was added. Set their access below.", "success")
            return redirect(url_for("user_profile", user_id=new_user["id"]))

    users.sort(key=lambda u: (not u.get("active", True), user_display_name(u).lower()))
    sheets = load_sheets_index()
    user_names = {u["id"]: user_display_name(u) for u in users}
    return render_template(
        "admin.html", users=users, roles=ROLES, error=error, form=form,
        sheets=sheets, user_names=user_names,
        sheet_candidates=[u for u in users if u.get("role") != "admin" and u.get("active", True)],
        sheet_admins=[u for u in users if u.get("role") == "admin" and u.get("active", True)],
        ledger_settings=load_settings(),
    )


@app.route("/users")
def users_page():
    """'Users' in the menu opens your own profile."""
    return redirect(url_for("user_profile", user_id=current_user()["id"]))


@app.route("/users/<user_id>", methods=["GET", "POST"])
def user_profile(user_id):
    me = current_user()
    is_admin = me.get("role") == "admin"
    is_self = me["id"] == user_id
    if not (is_admin or is_self):
        return render_template("no_access.html"), 403

    users = [normalize_user(u) for u in load_users()]
    target = next((u for u in users if u.get("id") == user_id), None)
    if not target:
        flash("User not found.", "danger")
        return redirect(url_for("admin_page") if is_admin else url_for("home"))

    error = None
    section = None  # which card the error belongs to

    if request.method == "POST":
        action = request.form.get("action")
        section = action

        if action == "profile":
            data, error = _clean_profile_form(request.form, users, editing_id=user_id)
            if not error:
                old_username = target["username"]
                target.update(data)
                save_users(users)
                append_ledger_entry("user_profile_updated", {"username": target["username"], "was": old_username, "by": me["username"]})
                flash("Personal info saved.", "success")
                return redirect(url_for("user_profile", user_id=user_id))

        elif action == "password":
            # Changing your own password needs the current one. Admins resetting someone else don't.
            if is_self and not check_password_hash(target["password_hash"], request.form.get("current_password", "")):
                error = "Current password is incorrect."
            else:
                error = _validate_new_password(request.form.get("password", ""), request.form.get("confirm", ""))
            if not error:
                target["password_hash"] = generate_password_hash(request.form["password"])
                save_users(users)
                append_ledger_entry("user_password_changed", {"username": target["username"], "by": me["username"]})
                flash("Password updated.", "success")
                return redirect(url_for("user_profile", user_id=user_id))

        elif action == "account" and is_admin:
            role = request.form.get("role", target["role"])
            active = request.form.get("active") == "1"
            if role not in ROLES:
                error = "Invalid role."
            elif target["role"] == "admin" and target.get("active", True) \
                    and (role != "admin" or not active) and _active_admin_count(users) <= 1:
                error = "This is the last active admin. Make someone else an admin first."
            else:
                changes = {}
                if role != target["role"]:
                    changes["role"] = role
                if active != target.get("active", True):
                    changes["active"] = active
                target["role"], target["active"] = role, active
                save_users(users)
                if changes:
                    append_ledger_entry("user_account_changed", {"username": target["username"], **changes, "by": me["username"]})
                flash("Role and status saved.", "success")
                return redirect(url_for("user_profile", user_id=user_id))

        elif action == "sheets" and is_admin:
            chosen = set(request.form.getlist("sheets"))
            sheets = load_sheets_index()
            changed = []
            for sh in sheets:
                if not sh.get("locked"):
                    continue  # unlocked sheets are open to everyone
                allowed = list(sh.get("allowed_users", []))
                has = target["id"] in allowed
                want = sh["id"] in chosen
                if want and not has:
                    allowed.append(target["id"])
                    changed.append(f"+{sh['name']}")
                elif has and not want:
                    allowed.remove(target["id"])
                    changed.append(f"-{sh['name']}")
                sh["allowed_users"] = allowed
            save_sheets_index(sheets)
            if changed:
                append_ledger_entry("user_sheets_changed", {"username": target["username"], "changes": changed, "by": me["username"]})
            flash("Sheet access saved.", "success")
            return redirect(url_for("user_profile", user_id=user_id))

        elif action == "access" and is_admin:
            features = [f for f in request.form.getlist("features") if f in FEATURE_KEYS]
            if request.form.get("all_locations") == "1":
                locations = "all"
            else:
                valid_ids = {loc.get("id") for loc in load_json(LOCATIONS_PATH, [])}
                locations = [l for l in request.form.getlist("locations") if l in valid_ids]
            target["features"] = features
            target["locations"] = locations
            save_users(users)
            append_ledger_entry("user_access_changed", {
                "username": target["username"], "features": features, "locations": locations, "by": me["username"],
            })
            flash("Access saved.", "success")
            return redirect(url_for("user_profile", user_id=user_id))

        else:
            error = "You can't change that."

    return render_template(
        "user_profile.html",
        user=target,
        is_admin=is_admin,
        is_self=is_self,
        roles=ROLES,
        features=FEATURES,
        all_locations=load_json(LOCATIONS_PATH, []),
        sheets=load_sheets_index(),
        can_spreadsheet=user_can(target, "spreadsheet"),
        error=error,
        section=section,
        form=request.form if error else {},
    )


@app.template_filter("datetimeformat")
def datetimeformat(value, fmt="%b %d, %Y — %I:%M %p"):
    """
    Jinja filter to format ISO datetime strings (or datetime objects)
    into a readable string like: 'Dec 22, 2025 — 04:32 PM'.
    """
    if not value:
        return ""

    try:
        # If it's already a datetime object
        if isinstance(value, datetime):
            return value.strftime(fmt)

        # Assume ISO string, handle a possible trailing 'Z'
        if isinstance(value, str):
            s = value.strip()
            if s.endswith("Z"):
                s = s[:-1]
            return datetime.fromisoformat(s).strftime(fmt)
    except Exception:
        # Fallback: if parsing fails, just return original value
        return value

    return value

@app.template_filter("unit_caps")
def unit_caps(u):
    """Display a unit string in ALL CAPS safely."""
    if not isinstance(u, str):
        return ""
    return u.upper()


# -------------------------
# Utilities: time
# -------------------------
CENTRAL_TZ = ZoneInfo("America/Chicago")

def now_central_iso():
    # ISO with timezone offset, stable for storage/logs
    return datetime.now(tz=CENTRAL_TZ).isoformat(timespec="seconds")

def now_central_str():
    # display-only (if you still want it)
    return datetime.now(tz=CENTRAL_TZ).strftime("%Y-%m-%d %H:%M")

def central_time_now_str():
    """
    Backwards-compatible helper.
    Many parts of the app still call central_time_now_str().
    Use ISO for storage/log consistency.
    """
    return now_central_iso()




# -------------------------
# Utilities: storage (atomic + self-healing)
# -------------------------
def _ensure_dir_for(path: str) -> None:
    os.makedirs(os.path.dirname(path), exist_ok=True)

def _atomic_write_json(path: str, data: Any) -> None:
    """
    Atomic JSON write:
    - writes to temp file in same directory
    - fsync
    - os.replace swap (atomic)
    Prevents corrupted JSON if the app crashes mid-write.
    """
    _ensure_dir_for(path)
    fd, tmp_path = tempfile.mkstemp(prefix=".tmp_", suffix=".json", dir=os.path.dirname(path))
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as f:
            json.dump(data, f, indent=2)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp_path, path)
    finally:
        try:
            if os.path.exists(tmp_path):
                os.remove(tmp_path)
        except Exception:
            pass

def load_json(path: str, default):
    """
    Safe JSON load:
    - creates missing files
    - if corrupt/unreadable, renames to .corrupt and resets to default
    """
    _ensure_dir_for(path)

    if not os.path.exists(path):
        _atomic_write_json(path, default)
        return default

    try:
        with open(path, "r", encoding="utf-8") as f:
            return json.load(f)
    except Exception:
        # keep a copy for debugging
        try:
            os.replace(path, path + ".corrupt")
        except Exception:
            pass
        _atomic_write_json(path, default)
        return default

def save_json(path: str, data) -> None:
    _atomic_write_json(path, data)


# ---------------------------------------------------------------------------
# Event ledger — append-only, hash-chained audit log.
# Every inventory-affecting event (receive, issue/blend draw, etc.) gets one
# entry here. Entries are never edited or deleted; corrections are new
# offsetting entries. entry_hash covers prev_hash + this entry's own data, so
# the whole chain can be replayed and verified.
# ---------------------------------------------------------------------------

GENESIS_HASH = "0" * 64


def load_ledger():
    return load_json(EVENT_LEDGER_PATH, [])


def _save_ledger(entries):
    save_json(EVENT_LEDGER_PATH, entries)


def _hash_entry(prev_hash: str, entry_id: str, event_type: str, timestamp: str, payload: Any) -> str:
    canonical = json.dumps(
        {
            "prev_hash": prev_hash,
            "entry_id": entry_id,
            "event_type": event_type,
            "timestamp": timestamp,
            "payload": payload,
        },
        sort_keys=True,
        separators=(",", ":"),
        default=str,
    )
    return hashlib.sha256(canonical.encode("utf-8")).hexdigest()


def append_ledger_entry(event_type: str, payload: dict) -> dict:
    """
    Append a new hash-chained entry to the event ledger and persist it.
    Returns the entry that was written.
    """
    entries = load_ledger()
    entry = _build_ledger_entry(entries, event_type, payload)
    entries.append(entry)
    _save_ledger(entries)
    return entry


def verify_ledger_chain(entries=None) -> dict:
    """
    Replays the chain and confirms every entry's stored hash matches a
    recomputed hash, and that prev_hash pointers line up. Returns a summary
    dict rather than raising, so a broken chain can be surfaced in the UI.
    """
    entries = entries if entries is not None else load_ledger()
    expected_prev = GENESIS_HASH
    for i, e in enumerate(entries):
        if e.get("prev_hash") != expected_prev:
            return {"ok": False, "broken_at": e.get("entry_id"), "reason": "prev_hash mismatch", "index": i}
        recomputed = _hash_entry(
            e.get("prev_hash"), e.get("entry_id"), e.get("event_type"), e.get("timestamp"), e.get("payload")
        )
        if recomputed != e.get("entry_hash"):
            return {"ok": False, "broken_at": e.get("entry_id"), "reason": "entry_hash mismatch", "index": i}
        expected_prev = e["entry_hash"]
    return {"ok": True, "count": len(entries)}

def load_products():
    data = load_json(DATA_PATH, [])

    # normalize into list[dict]
    if isinstance(data, list):
        products = data
    elif isinstance(data, dict):
        if isinstance(data.get("products"), list):
            products = data["products"]
        else:
            products = list(data.values())
    else:
        products = []

    # normalize unit fields for consistency
    for p in products:
        if not isinstance(p, dict):
            continue
        if isinstance(p.get("unit"), str):
            p["unit"] = unit_to_display(p["unit"])
        if isinstance(p.get("default_unit"), str):
            p["default_unit"] = unit_to_display(p["default_unit"])

    return products

def save_products(products):
    # enforce ALL CAPS on unit/default_unit before persisting
    for p in products:
        if not isinstance(p, dict):
            continue
        if isinstance(p.get("unit"), str):
            p["unit"] = unit_to_display(p["unit"])
        if isinstance(p.get("default_unit"), str):
            p["default_unit"] = unit_to_display(p["default_unit"])

    save_json(DATA_PATH, products)

# ---- Tanks ----
def load_tanks():
    return load_json(TANKS_PATH, [])

def save_tanks(tanks):
    save_json(TANKS_PATH, tanks)

# ---- Tank Ledger ----
def load_tank_ledger():
    return load_json(TANK_LEDGER_PATH, [])

def save_tank_ledger(rows):
    save_json(TANK_LEDGER_PATH, rows)

# ---- Blends ----
def load_blends():
    return load_json(BLENDS_PATH, [])

def save_blends(blends):
    save_json(BLENDS_PATH, blends)

# ---- Alerts ----
def load_alerts():
    return load_json(ALERTS_PATH, [])

def save_alerts(alerts):
    save_json(ALERTS_PATH, alerts)

# ---- Staging ----
def load_staging():
    return load_json(STAGING_PATH, [])

def save_staging(records):
    save_json(STAGING_PATH, records)

# ---- Locations ----
def load_locations():
    return load_json(LOCATIONS_PATH, [])

def save_locations(locations):
    save_json(LOCATIONS_PATH, locations)

# ---- Formulas ----
def load_formulas():
    return load_json(FORMULAS_PATH, [])

def save_formulas(formulas):
    save_json(FORMULAS_PATH, formulas)

def get_formula_by_id(formulas, formula_id):
    formula_id = str(formula_id)
    return next((f for f in formulas if str(f.get("id")) == formula_id), None)


# ---- Packages (definitions) ----
def load_packages():
    return load_json(PACKAGES_PATH, [])

def save_packages(packages):
    save_json(PACKAGES_PATH, packages)

def get_package_by_id(packages, package_id):
    package_id = str(package_id)
    return next((pk for pk in packages if str(pk.get("id")) == package_id), None)

def generate_next_package_id(packages):
    max_n = 0
    for pk in packages:
        pid = str(pk.get("id", ""))
        if pid.startswith("PKG") and pid[3:].isdigit():
            max_n = max(max_n, int(pid[3:]))
    return f"PKG{max_n + 1:04d}"

# ---- Package Inventory (tracked receive records) ----
def load_package_inventory():
    return load_json(PACKAGE_INVENTORY_PATH, [])

def save_package_inventory(records):
    save_json(PACKAGE_INVENTORY_PATH, records)

def generate_next_pki_id(records):
    max_n = 0
    for r in records:
        rid = str(r.get("id", ""))
        if rid.startswith("PKI") and rid[3:].isdigit():
            max_n = max(max_n, int(rid[3:]))
    return f"PKI{max_n + 1:06d}"

def get_package_inventory_summary(product_id):
    """
    Roll up all PKI records for a product into per-package-type totals.
    Returns dict keyed by package_id:
      { package_id: { package_id, package_name, volume_per, unit, quantity, total_volume } }
    """
    records = load_package_inventory()
    packages = load_packages()
    pkg_by_id = {str(pk.get("id")): pk for pk in packages}

    totals = {}
    for r in records:
        if str(r.get("product_id")) != str(product_id):
            continue
        pid = str(r.get("package_id"))
        pkg = pkg_by_id.get(pid)
        if not pkg:
            continue
        qty = float(r.get("quantity") or 0.0)
        vol_per = float(r.get("volume_per") or pkg.get("volume") or 0.0)

        if pid not in totals:
            totals[pid] = {
                "package_id":   pid,
                "package_name": pkg.get("name", pid),
                "volume_per":   vol_per,
                "unit":         r.get("unit") or pkg.get("unit") or "gal",
                "quantity":     0.0,
                "total_volume": 0.0,
            }
        totals[pid]["quantity"]     += qty
        totals[pid]["total_volume"] += qty * vol_per

    return totals


def get_package_inventory_summary_for_location(product_id, location_id):
    """
    Same rollup as get_package_inventory_summary(), but scoped to a single
    location_id. Powers the per-location package breakdown on the
    Location Detail page (mirrors list_products.html's pkg_summaries).

    Returns dict keyed by package_id:
      { package_id: { package_id, package_name, volume_per, unit, quantity, total_volume } }
    """
    if not location_id:
        return {}

    records = load_package_inventory()
    packages = load_packages()
    pkg_by_id = {str(pk.get("id")): pk for pk in packages}

    totals = {}
    for r in records:
        if str(r.get("product_id")) != str(product_id):
            continue
        if str(r.get("location_id") or "") != str(location_id):
            continue
        pid = str(r.get("package_id"))
        pkg = pkg_by_id.get(pid)
        if not pkg:
            continue
        qty = float(r.get("quantity") or 0.0)
        vol_per = float(r.get("volume_per") or pkg.get("volume") or 0.0)

        if pid not in totals:
            totals[pid] = {
                "package_id":   pid,
                "package_name": pkg.get("name", pid),
                "volume_per":   vol_per,
                "unit":         r.get("unit") or pkg.get("unit") or "gal",
                "quantity":     0.0,
                "total_volume": 0.0,
            }
        totals[pid]["quantity"]     += qty
        totals[pid]["total_volume"] += qty * vol_per

    return totals


def get_packaged_default_qty_for_location(prod, location_id):
    """
    Net packaged quantity, converted into the product's default unit,
    currently recorded at a specific location (receives minus any
    sales/removals of packaged units). This does NOT reflect a deduction
    from bulk FIFO — packaging is just a different view of the same
    physical inventory, so this figure is used only to work out how much
    of the bulk total is still "Unpackaged" (see Unpackaged calculations
    in list_products/location_detail routes and in the repackage flow).
    """
    if not location_id:
        return 0.0

    product_id = str(prod.get("id"))
    records = load_package_inventory()

    total_default = 0.0
    for r in records:
        if str(r.get("product_id")) != product_id:
            continue
        if str(r.get("location_id") or "") != str(location_id):
            continue
        vol = float(r.get("total_volume") or 0.0)
        unit = r.get("unit") or "gal"
        try:
            total_default += convert_to_product_default_unit(prod, vol, unit)
        except Exception:
            # Can't reliably convert (e.g. missing weight) — skip rather
            # than corrupt the total with a bad unit assumption.
            continue

    return total_default


def compute_location_inventory(location_id):
    """
    Roll up bulk (FIFO layer) qty AND packaged (PKI ledger) qty for every
    product at a single location. Powers the location browser panel on the
    Adjust Inventory page.

    Returns:
      {
        "location_id": "...",
        "location_name": "...",
        "products": [
          {
            "product_id": ..., "product_name": ...,
            "bulk_qty": 12.5, "unit": "gal",
            "packages": [ {package_id, package_name, quantity, unit}, ... ],
          }, ...
        ]
      }
    Only products with nonzero bulk qty or at least one nonzero package
    quantity at this location are included.
    """
    locations = load_locations_safe()
    loc = get_location_by_id(locations, location_id)
    loc_name = (loc or {}).get("name") or ""
    loc_name_norm = loc_name.strip().lower()

    products = load_products()

    # ---- Bulk qty per product at this location, from FIFO layers ----
    bulk_by_product = {}
    for p in products:
        _ensure_layers(p)
        total = 0.0
        for layer in (p.get("layers") or []):
            layer_loc = (layer.get("location") or p.get("location") or "UNASSIGNED").strip()
            if layer_loc.lower() == loc_name_norm:
                total += float(layer.get("qty") or 0.0)
        if total:
            bulk_by_product[str(p.get("id"))] = round(total, 4)

    # ---- Packaged qty per product/package at this location, from PKI ledger ----
    packages = load_packages()
    pkg_by_id = {str(pk.get("id")): pk for pk in packages}

    records = load_package_inventory()
    pkg_totals = {}  # product_id -> package_id -> {package_id, package_name, unit, quantity}
    for r in records:
        if str(r.get("location_id") or "") != str(location_id):
            continue
        pid = str(r.get("product_id"))
        kid = str(r.get("package_id"))
        pkg_def = pkg_by_id.get(kid)
        if not pkg_def:
            continue
        qty = float(r.get("quantity") or 0.0)
        bucket = pkg_totals.setdefault(pid, {})
        entry = bucket.setdefault(kid, {
            "package_id": kid,
            "package_name": pkg_def.get("name", kid),
            "unit": (pkg_def.get("unit") or "unit"),
            "quantity": 0.0,
        })
        entry["quantity"] += qty

    # ---- Merge into per-product rows ----
    prod_by_id = {str(p.get("id")): p for p in products}
    product_ids = set(bulk_by_product.keys()) | set(pkg_totals.keys())

    out_products = []
    for pid in product_ids:
        prod = prod_by_id.get(pid)
        if not prod:
            continue
        bulk_qty = bulk_by_product.get(pid, 0.0)
        pkgs = [v for v in pkg_totals.get(pid, {}).values() if round(v["quantity"], 4) != 0]
        for v in pkgs:
            v["quantity"] = round(v["quantity"], 4)
        pkgs.sort(key=lambda x: x["package_name"].lower())

        if bulk_qty == 0 and not pkgs:
            continue

        out_products.append({
            "product_id": pid,
            "product_name": prod.get("name") or pid,
            "bulk_qty": bulk_qty,
            "unpackaged_qty": round(
                max(0.0, bulk_qty - get_packaged_default_qty_for_location(prod, location_id)), 4
            ),
            "unit": normalize_unit(prod.get("default_unit")),
            "weight": prod.get("weight"),  # lb/gal — lets the frontend convert GAL <-> LB
            "packages": pkgs,
        })

    out_products.sort(key=lambda x: x["product_name"].lower())

    return {
        "location_id": str(location_id),
        "location_name": loc_name,
        "products": out_products,
    }


def deduct_package_inventory(product_id, package_rows, location_id, location_name, notes, ref_type="sale"):
    """
    Append negative ledger entries to package_inventory.json to record
    packaged units being sold/removed (e.g. selling full totes/drums/cases).
    Does NOT touch bulk product layers — that's handled separately via
    fifo_issue_from_location / stage_create using the bulk-equivalent qty.

    package_rows: list of {package_id, package_name, qty, volume_per, unit}
    """
    if not package_rows:
        return

    pki_records = load_package_inventory()
    for row in package_rows:
        pqty = float(row.get("qty") or 0.0)
        if pqty <= 0:
            continue
        vol_per = float(row.get("volume_per") or 0.0)
        pki_records.append({
            "id":            generate_next_pki_id(pki_records),
            "product_id":    str(product_id),
            "package_id":    row.get("package_id"),
            "package_name":  row.get("package_name"),
            "quantity":      -pqty,
            "volume_per":    vol_per,
            "unit":          row.get("unit") or "gal",
            "total_volume":  -pqty * vol_per,
            "location_id":   location_id,
            "location_name": location_name,
            "received_at":   None,
            "removed_at":    now_central_iso(),
            "type":          ref_type,  # "sale" | "staged_sale"
            "notes":         notes,
        })
    save_package_inventory(pki_records)


# -------------------------
# Storage: ensure JSON stores exist (used at startup)
# -------------------------
def ensure_data_store():
    """Ensure products.json exists and is a list."""
    load_json(DATA_PATH, [])

def ensure_locations_store():
    """Ensure locations.json exists and is a list."""
    load_json(LOCATIONS_PATH, [])

def ensure_tanks_store():
    """Ensure tanks.json exists and is a list."""
    load_json(TANKS_PATH, [])

def ensure_tank_ledger_store():
    """Ensure tank_ledger.json exists and is a list."""
    load_json(TANK_LEDGER_PATH, [])

def ensure_formulas_store():
    """Ensure formulas.json exists and is a list."""
    load_json(FORMULAS_PATH, [])

def ensure_packages_store():
    """Ensure packages.json exists and is a list."""
    load_json(PACKAGES_PATH, [])

def ensure_package_inventory_store():
    """Ensure package_inventory.json exists and is a list."""
    load_json(PACKAGE_INVENTORY_PATH, [])


#---End of Chunk 1---

#---Start of Chunk 2---
# -------------------------
# Locations Storage
# -------------------------
def _to_float(x, default=0.0):
    try:
        return float(str(x).strip())
    except Exception:
        return default

def _safe_str(x):
    return (x or "").strip()

@app.route("/locations/add", methods=["GET", "POST"])
def add_location():
    locations = load_locations()

    if request.method == "GET":
        return render_template(
            "add_location.html",
            form={},
            errors=[]
        )

    # ---- POST ----
    errors = []

    name = _safe_str(request.form.get("name"))
    address = _safe_str(request.form.get("address"))

    # Optional tanks entered while creating the location
    tank_names = request.form.getlist("tank_name[]")
    tank_caps = request.form.getlist("tank_capacity_gal[]")
    tank_notes = request.form.getlist("tank_notes[]")

    if not name:
        errors.append("Location name is required.")

    # prevent duplicate names (helpful)
    if name and any((loc.get("name", "").strip().lower() == name.lower()) for loc in locations):
        errors.append("A location with that name already exists.")

    # Create location id
    loc_id = uuid.uuid4().hex[:10]

    # -------------------------
    # 1) VALIDATE tanks (NO save yet)
    # -------------------------
    tanks_to_create = []
    if not errors:
        # Load tanks once (needed for ID generation)
        existing_tanks = load_tanks()

        # We'll generate IDs off a working list so each new tank gets a unique sequential ID
        working_tanks = list(existing_tanks)

        for nm, cap_raw, note in zip(tank_names, tank_caps, tank_notes):
            nm = (nm or "").strip()
            cap_raw = (cap_raw or "").strip()
            note = (note or "").strip() or None

            if not nm:
                continue  # blank line = ignore

            try:
                cap = float(cap_raw)
                if cap <= 0:
                    errors.append(f"Tank '{nm}' capacity must be greater than 0.")
                    continue
            except Exception:
                errors.append(f"Tank '{nm}' capacity must be a number.")
                continue

            new_tid = generate_next_tank_id(working_tanks)

            tank_obj = {
                "id": new_tid,
                "location_id": str(loc_id),
                "name": nm,
                "capacity_gal": float(cap),
                "assigned_product_id": None,
                "is_active": True,
                "notes": note,
                "created_at": now_central_iso(),
            }

            tanks_to_create.append(tank_obj)
            working_tanks.append(tank_obj)

    # If ANY errors, do not save anything
    if errors:
        return render_template(
            "add_location.html",
            form=request.form.to_dict(),
            errors=errors
        )

    # -------------------------
    # 2) APPLY changes (mutations) + SAVE (atomic-ish)
    # -------------------------

    # Create location record
    new_loc = {
        "id": loc_id,
        "name": name,
        "address": address,
        "created_at": datetime.now(timezone.utc).isoformat()
    }

    # Save location
    locations.append(new_loc)
    save_locations(locations)

    # Save tanks (if any)
    if tanks_to_create:
        tanks = load_tanks()  # re-load, append, save
        tanks.extend(tanks_to_create)
        save_tanks(tanks)

    flash("Location created.", "success")
    return redirect(url_for("locations_page"))


def generate_next_tank_id(tanks):
    """
    Generates sequential tank IDs like TK0001, TK0002...
    """
    max_n = 0
    for t in tanks:
        tid = str(t.get("id", ""))
        if tid.startswith("TK") and tid[2:].isdigit():
            max_n = max(max_n, int(tid[2:]))
    return f"TK{max_n+1:04d}"

def generate_next_tx_id(ledger_rows):
    """
    Generates sequential transaction IDs like TX000001, TX000002...
    """
    max_n = 0
    for r in ledger_rows:
        rid = str(r.get("id", ""))
        if rid.startswith("TX") and rid[2:].isdigit():
            max_n = max(max_n, int(rid[2:]))
    return f"TX{max_n+1:06d}"

def get_tank_by_id(tanks, tank_id):
    tank_id = str(tank_id)
    return next((t for t in tanks if str(t.get("id")) == tank_id), None)

def get_tanks_for_location(tanks, location_id):
    location_id = str(location_id)
    return [t for t in tanks if str(t.get("location_id")) == location_id and t.get("is_active", True)]

def compute_product_location_breakdown(prod: dict):
    """
    Roll up THIS product's FIFO layers into totals by location.
    Returns list of rows:
      [{location, qty, unit, value, avg_cost}, ...]
    """
    _ensure_layers(prod)

    default_unit = normalize_unit(prod.get("default_unit"))
    rows_map = {}

    for layer in (prod.get("layers") or []):
        loc = (layer.get("location") or prod.get("location") or "UNASSIGNED").strip() or "UNASSIGNED"
        qty = float(layer.get("qty") or 0.0)
        cost = float(layer.get("unit_cost") or 0.0)

        if loc not in rows_map:
            rows_map[loc] = {"location": loc, "qty": 0.0, "value": 0.0}

        rows_map[loc]["qty"] += qty
        rows_map[loc]["value"] += qty * cost

    # build final rows with avg cost
    out = []
    for loc, d in rows_map.items():
        q = float(d["qty"])
        v = float(d["value"])
        avg = (v / q) if q > 0 else 0.0
        out.append(
            {
                "location": loc,
                "qty": round(q, 4),
                "unit": default_unit,
                "value": round(v, 2),
                "avg_cost": round(avg, 4),
            }
        )

    # sort biggest qty first (or alphabetical if you want)
    out.sort(key=lambda r: r["qty"], reverse=True)
    return out

def _safe_float(x, default=0.0):
    try:
        return float(x)
    except Exception:
        return default

def get_tank_fill_gal(ledger_rows, tank_id):
    """
    Current gallons in tank = sum(delta_gal) across ledger rows for that tank.
    """
    tank_id = str(tank_id)
    total = 0.0
    for r in ledger_rows:
        if str(r.get("tank_id")) == tank_id:
            total += _safe_float(r.get("delta_gal"), 0.0)
    # clamp tiny negatives due to float drift
    if abs(total) < 1e-9:
        total = 0.0
    return total

def is_tank_empty(ledger_rows, tank_id):
    return get_tank_fill_gal(ledger_rows, tank_id) <= 1e-9

def gallons_from_input(qty, unit, product):
    """
    Convert a user-entered qty+unit into gallons.
    - If unit is gal -> same
    - If unit is lb -> requires product['weight'] (lb/gal): gal = lb / (lb_per_gal)
    """
    unit = (unit or "").strip().lower()
    qty_f = _safe_float(qty, 0.0)

    if unit == "gal":
        return qty_f

    if unit == "lb":
        lb_per_gal = product.get("weight", None)
        if lb_per_gal is None or _safe_float(lb_per_gal, 0.0) <= 0:
            raise ValueError("This product needs Weight (LB/GAL) to convert LB → GAL for tank storage.")
        return qty_f / float(lb_per_gal)

    raise ValueError("Tank storage only supports units GAL or LB (conversion to gallons).")

def tank_status(fill_gal, capacity_gal, near_empty_pct=0.10, near_full_pct=0.90):
    """
    Returns: (pct_full, label)
    label in: empty, near_empty, ok, near_full, full
    """
    cap = max(_safe_float(capacity_gal, 0.0), 0.0)
    if cap <= 0:
        return (0.0, "ok")
    pct = fill_gal / cap
    if fill_gal <= 1e-9:
        return (0.0, "empty")
    if pct >= 1.0 - 1e-9:
        return (1.0, "full")
    if pct >= near_full_pct:
        return (pct, "near_full")
    if pct <= near_empty_pct:
        return (pct, "near_empty")
    return (pct, "ok")
def apply_tank_receive(
    tank_id,
    product,
    qty_in,
    unit_in,
    source="receive",
    ref=None,
    notes=None
):
    """
    Add inventory into a tank (in gallons).
    Enforces:
      - capacity (gallons)
      - product lock: tank holds one product until empty
    Updates:
      - writes tank ledger transaction
      - sets tank.assigned_product_id when tank was empty

    Returns: dict with { "delta_gal", "fill_before", "fill_after", "capacity_gal", "status_label", "pct_full" }
    """
    tanks = load_tanks()
    ledger = load_tank_ledger()

    tank = get_tank_by_id(tanks, tank_id)
    if not tank:
        raise ValueError("Selected tank was not found.")

    capacity_gal = _safe_float(tank.get("capacity_gal"), 0.0)
    if capacity_gal <= 0:
        raise ValueError("Tank capacity must be > 0 gallons.")

    fill_before = get_tank_fill_gal(ledger, tank_id)

    # tank locking: if tank not empty, must match assigned product
    assigned_pid = tank.get("assigned_product_id") or None
    product_id = str(product.get("id"))

    if fill_before > 1e-9:
        if assigned_pid and str(assigned_pid) != product_id:
            raise ValueError("This tank currently holds a different product. Empty it before storing another product.")
    else:
        # tank empty: lock to this product when receiving
        tank["assigned_product_id"] = product_id

    delta_gal = gallons_from_input(qty_in, unit_in, product)
    if delta_gal <= 0:
        raise ValueError("Quantity must be > 0 to receive into a tank.")

    if fill_before + delta_gal > capacity_gal + 1e-9:
        raise ValueError("Not enough capacity in tank for this receipt.")

    # write ledger row
    tx_id = generate_next_tx_id(ledger)
    row = {
        "id": tx_id,
        "ts": now_central_iso(),   # uses your existing function
        "tank_id": str(tank_id),
        "product_id": product_id,
        "delta_gal": float(delta_gal),
        "source": source,
        "ref": ref,
        "notes": notes
    }
    ledger.append(row) 

    # save tank (maybe updated assigned product)
    save_tanks(tanks)
    save_tank_ledger(ledger)

    fill_after = fill_before + delta_gal
    pct, label = tank_status(fill_after, capacity_gal)

    return {
        "delta_gal": float(delta_gal),
        "fill_before": float(fill_before),
        "fill_after": float(fill_after),
        "capacity_gal": float(capacity_gal),
        "status_label": label,
        "pct_full": float(pct),
    }

def apply_tank_issue(
    tank_id,
    product,
    qty_out,
    unit_out,
    source="issue",
    ref=None,
    notes=None
):
    """
    Remove inventory from a tank (in gallons).
    Enforces:
      - tank must contain this product
      - cannot issue more than current fill
    Writes:
      - negative delta_gal row to tank ledger
    """

    tanks = load_tanks()
    ledger = load_tank_ledger()

    tank = get_tank_by_id(tanks, tank_id)
    if not tank:
        raise ValueError("Selected tank was not found.")

    fill_before = get_tank_fill_gal(ledger, tank_id)
    if fill_before <= 1e-9:
        raise ValueError("Tank is empty.")

    assigned_pid = tank.get("assigned_product_id")
    product_id = str(product.get("id"))

    if assigned_pid and str(assigned_pid) != product_id:
        raise ValueError("This tank contains a different product.")

    delta_gal = gallons_from_input(qty_out, unit_out, product)
    if delta_gal <= 0:
        raise ValueError("Quantity must be > 0.")

    if delta_gal > fill_before + 1e-9:
        raise ValueError("Not enough volume in tank.")

    tx_id = generate_next_tx_id(ledger)
    ledger.append({
        "id": tx_id,
        "ts": now_central_iso(),
        "tank_id": str(tank_id),
        "product_id": product_id,
        "delta_gal": -float(delta_gal),
        "source": source,
        "ref": ref,
        "notes": notes,
    })

    save_tank_ledger(ledger)
    # if tank is now empty, unlock it
    maybe_unlock_tank_if_empty(tank_id) 


    return {
        "delta_gal": -float(delta_gal),
        "fill_before": float(fill_before),
        "fill_after": float(fill_before - delta_gal),
    }

def apply_tank_transfer(
    from_tank_id,
    to_tank_id,
    product,
    qty,
    unit,
    source="move",
    ref=None,
    notes=None
):
    if from_tank_id:
        apply_tank_issue(
            tank_id=from_tank_id,
            product=product,
            qty_out=qty,
            unit_out=unit,
            source=f"{source}_out",
            ref=ref,
            notes=notes,
        )

    if to_tank_id:
        apply_tank_receive(
            tank_id=to_tank_id,
            product=product,
            qty_in=qty,
            unit_in=unit,
            source=f"{source}_in",
            ref=ref,
            notes=notes,
        )

    if from_tank_id:
        maybe_unlock_tank_if_empty(from_tank_id)


def maybe_unlock_tank_if_empty(tank_id):
    tanks = load_tanks()
    ledger = load_tank_ledger()

    tank = get_tank_by_id(tanks, tank_id)
    if not tank:
        return

    if is_tank_empty(ledger, tank_id):
        tank["assigned_product_id"] = None
        save_tanks(tanks)


def load_locations_safe():
    """
    Uses your existing locations loader if present.
    If you named it differently, swap it here.
    """
    try:
        return load_locations()
    except NameError:
        # If you don't have locations yet, keep app from crashing.
        return []

def get_location_by_id(locations, location_id):
    location_id = str(location_id)
    return next((l for l in locations if str(l.get("id")) == location_id), None)

def product_name_by_id(products, product_id):
    product_id = str(product_id)
    p = next((x for x in products if str(x.get("id")) == product_id), None)
    return (p or {}).get("name") or None

#---End of Chunk 2---

# -------------------------
# Helpers: product lookup & IDs
# -------------------------
def get_product_by_id(products, product_id):
    for i, p in enumerate(products):
        if p.get("id") == product_id:
            return i, p
    return None, None


def _get_product(products, product_id):
    for p in products:
        if p.get("id") == product_id:
            return p
    return None


def generate_next_product_id(products):
    """
    Next numeric ID, min 4 digits, zero-padded:
    0001, 0002, ... 0999, 1000, 1001, ...
    Ignores non-numeric IDs.
    """
    numeric_ids = []
    iterable = products.values() if isinstance(products, dict) else (products or [])
    for p in iterable:
        if not isinstance(p, dict):
            continue
        pid = str(p.get("id") or "").strip()
        if pid.isdigit():
            try:
                numeric_ids.append(int(pid))
            except ValueError:
                pass

    next_int = (max(numeric_ids) + 1) if numeric_ids else 1
    s = str(next_int)
    return s.zfill(4) if len(s) < 4 else s


# -------------------------
# Utilities: calculations
# -------------------------
def to_pounds(weight_lb_per_gal: float, qty_gal: float) -> float:
    return float(weight_lb_per_gal) * float(qty_gal)


def to_gallons(weight_lb_per_gal: float, qty_lb: float) -> float:
    w = float(weight_lb_per_gal)
    if w <= 0:
        return 0.0
    return float(qty_lb) / w


def inventory_value(unit_cost: float, quantity: float) -> float:
    return float(unit_cost) * float(quantity)


def packages_from_gallons(gallons, package_size_gal):
    if gallons is None:
        return None
    if not package_size_gal or float(package_size_gal) <= 0:
        return None
    return float(gallons) / float(package_size_gal)


# -------------------------
# Units & display helpers
# -------------------------
def normalize_unit(u: str) -> str:
    """
    Map common aliases (tote/drum/cooler/ea/etc.) to 'unit'
    """
    u = (u or "").strip().lower()
    if u in {"gallon", "gallons", "gal"}:
        return "gal"
    if u in {"pound", "pounds", "lb", "lbs"}:
        return "lb"
    if u in {"unit", "units", "ea", "each", "tote", "totes", "drum", "drums", "cooler", "coolers", "ibc", "ibcs"}:
        return "unit"
    return u or "unit"



def unit_to_display(u: str) -> str:
    """
    Display helper: canonical ALL-CAPS unit strings used across templates & storage.
    Accepts common aliases via normalize_unit().
    Examples:
      'gallons' -> 'GAL'
      'lb'      -> 'LB'
      'tote'    -> 'UNIT'
    """
    if u is None:
        return "UNIT"
    return normalize_unit(str(u)).upper()

def compute_display_breakdown(p):
    """
    Returns (gallons, pounds) for display based on default_unit.
    - 'unit' products do not convert.
    """
    default_unit = normalize_unit(p.get("default_unit"))
    qty = float(p.get("quantity") or 0.0)

    wpg = p.get("weight")
    try:
        wpg_val = float(wpg) if wpg not in (None, "") else None
    except Exception:
        wpg_val = None

    gallons = pounds = None
    if default_unit == "gal":
        gallons = qty
        if wpg_val:
            pounds = round(qty * wpg_val, 2)
    elif default_unit == "lb":
        pounds = qty
        if wpg_val and wpg_val != 0:
            gallons = round(qty / wpg_val, 2)
    return gallons, pounds


def package_volume_to_gallons(prod, amount, unit):
    """
    Convert a package-ledger amount (given in `unit`, the package's own
    unit of measure — usually 'gal') into gallons, using the product's
    weight (lb/gal) when the package is tracked in lb. Falls back to 0 for
    'unit'-tracked packages with no reliable gallons equivalent.

    This is used to compute how many gallons are currently "packaged" so
    Unpackaged = total gallons - packaged gallons can be shown consistently,
    regardless of what unit an individual package type happens to use.
    """
    unit = normalize_unit(unit or "gal")
    amount = float(amount or 0.0)
    if unit == "gal":
        return amount
    if unit == "lb":
        try:
            w = float(prod.get("weight") or 0.0)
        except (TypeError, ValueError):
            w = 0.0
        if w > 0:
            return amount / w
        return 0.0
    return 0.0


def compute_item_value(p) -> float:
    try:
        qty = float(p.get("quantity") or 0.0)
    except Exception:
        qty = 0.0
    try:
        cost = float(p.get("unit_cost") or 0.0)
    except Exception:
        cost = 0.0
    return round(qty * cost, 2)

# layers system
def _ensure_layers(prod: dict):
    """
    Ensure prod["layers"] exists and is clean.

    Each layer tracks:
      {
        "qty": float,
        "unit": "gal|lb|unit",
        "unit_cost": float,
        "datetime": "YYYY-MM-DD HH:MM",
        "location": str  # e.g. 'Midland Yard'
      }
    """
    layers = prod.get("layers")
    if not isinstance(layers, list):
        prod["layers"] = []

    # base location fallback for this product
    base_loc = (prod.get("location") or "UNASSIGNED").strip() or "UNASSIGNED"

    cleaned = []
    for l in prod["layers"]:
        if not isinstance(l, dict):
            continue

        # Accept older keys and normalize them
        raw_qty = l.get("qty") if "qty" in l else l.get("quantity")
        raw_cost = l.get("unit_cost") if "unit_cost" in l else l.get("cost_per_unit")

        try:
            q = float(raw_qty or 0.0)
            c = float(raw_cost or 0.0)
        except Exception:
            continue

        if q > 0:
            cleaned.append(
                {
                    "qty": round(q, 4),
                    "unit": normalize_unit(l.get("unit") or prod.get("default_unit")),
                    "unit_cost": round(c, 4),
                    # support old key name "received_at"
                    "datetime": (
                        l.get("datetime")
                        or l.get("received_at")
                        or prod.get("last_updated")
                        or central_time_now_str()
                    ),
                    "location": (l.get("location") or base_loc).strip() or "UNASSIGNED",
                }
            )

    prod["layers"] = cleaned



def _layers_total_qty(prod: dict) -> float:
    _ensure_layers(prod)
    return float(sum(float(l["qty"]) for l in prod["layers"]))


def _layers_total_value(prod: dict) -> float:
    _ensure_layers(prod)
    return float(sum(float(l["qty"]) * float(l["unit_cost"]) for l in prod["layers"]))


def _sync_product_qty_and_avg_cost_from_layers(prod: dict):
    _ensure_layers(prod)
    total_qty = _layers_total_qty(prod)
    total_val = _layers_total_value(prod)

    prod["quantity"] = round(total_qty, 4)
    avg = (total_val / total_qty) if total_qty > 0 else float(prod.get("unit_cost") or 0.0)
    prod["unit_cost"] = round(float(avg), 4)


def fifo_receive(prod: dict, qty_default: float, recv_cost: float, location: str | None = None):
    _ensure_layers(prod)
    qty_default = float(qty_default)
    recv_cost = float(recv_cost)
    if qty_default <= 0:
        return

    loc = (location or "").strip()
    if not loc:
        raise ValueError(f"A location is required to receive {prod.get('name') or 'inventory'}.")

    prod["layers"].append(
        {
            "qty": round(qty_default, 4),
            "unit": normalize_unit(prod.get("default_unit")),
            "unit_cost": round(recv_cost, 4),
            "datetime": now_central_iso(),
            "location": loc,
        }
    )
    _sync_product_qty_and_avg_cost_from_layers(prod)

    append_ledger_entry(
        "receive",
        {
            "product_id": prod.get("id"),
            "product_name": prod.get("product") or prod.get("name"),
            "qty": round(qty_default, 4),
            "unit_cost": round(recv_cost, 4),
            "location": loc,
        },
    )



def fifo_issue(prod: dict, qty_default: float) -> dict:
    _ensure_layers(prod)
    qty_default = float(qty_default)
    if qty_default <= 0:
        return {"issued_qty": 0.0, "issued_value": 0.0, "pulls": [], "effective_unit_cost": 0.0}

    on_hand = _layers_total_qty(prod)
    if qty_default > on_hand + 1e-9:
        raise ValueError(f"Not enough inventory to issue {qty_default:.4f}; on hand {on_hand:.4f}")

    remaining = qty_default
    pulls = []
    issued_value = 0.0

    while remaining > 1e-12 and prod["layers"]:
        layer = prod["layers"][0]
        layer_qty = float(layer["qty"])
        layer_cost = float(layer["unit_cost"])

        take = min(layer_qty, remaining)
        pulls.append({"qty": round(take, 4), "unit_cost": round(layer_cost, 4),
                      "location": layer.get("location")})
        issued_value += take * layer_cost

        layer["qty"] = layer_qty - take
        remaining -= take

        if layer["qty"] <= 1e-9:
            prod["layers"].pop(0)

    _sync_product_qty_and_avg_cost_from_layers(prod)
    eff_cost = (issued_value / qty_default) if qty_default > 0 else 0.0

    append_ledger_entry(
        "issue",
        {
            "product_id": prod.get("id"),
            "product_name": prod.get("product") or prod.get("name"),
            "qty": round(qty_default, 4),
            "pulls": pulls,
            "effective_unit_cost": round(eff_cost, 4),
        },
    )

    return {
        "issued_qty": round(qty_default, 4),
        "issued_value": round(issued_value, 4),
        "pulls": pulls,
        "effective_unit_cost": round(eff_cost, 4),
    }


def fifo_return(prod: dict, pulls: list, location: str | None = None):
    _ensure_layers(prod)
    if not pulls:
        return

    unit = normalize_unit(prod.get("default_unit"))
    # Each pull goes back to the location it came from; older pulls that didn't
    # record one fall back to the location passed in, then the product's location.
    base_loc = (location or prod.get("location") or "").strip()

    back = []
    for p in pulls:
        try:
            q = float(p.get("qty") or 0.0)
            c = float(p.get("unit_cost") or 0.0)
        except Exception:
            continue
        if q <= 0:
            continue
        loc = (p.get("location") or "").strip() or base_loc
        if not loc:
            raise ValueError(f"Can't tell which location to return {prod.get('name') or 'inventory'} to.")
        back.append((q, c, loc))

    # insert oldest-last so the returned layers keep their original FIFO order at the front
    for q, c, loc in reversed(back):
        prod["layers"].insert(
            0,
            {
                "qty": round(q, 4),
                "unit": unit,
                "unit_cost": round(c, 4),
                "datetime": now_central_iso(),
                "location": loc,
            },
        )

    _sync_product_qty_and_avg_cost_from_layers(prod)
def fifo_issue_from_location(prod: dict, qty_default: float, location_name: str) -> dict:
    """
    FIFO issue but only pulls from layers whose layer['location'] matches location_name.
    Returns same structure as fifo_issue plus 'location' used.
    """
    _ensure_layers(prod)
    qty_default = float(qty_default)
    if qty_default <= 0:
        return {"issued_qty": 0.0, "issued_value": 0.0, "pulls": [], "effective_unit_cost": 0.0}

    loc_key = (location_name or "UNASSIGNED").strip().lower()

    available = sum(float(l["qty"]) for l in prod["layers"]
                    if (l.get("location") or "").strip().lower() == loc_key)

    if qty_default > available + 1e-9:
        raise ValueError(f"Not enough inventory at {location_name}. Need {qty_default:.4f}, available {available:.4f}")

    remaining = qty_default
    pulls = []
    issued_value = 0.0

    i = 0
    while remaining > 1e-12 and i < len(prod["layers"]):
        layer = prod["layers"][i]
        layer_loc = (layer.get("location") or "").strip().lower()
        if layer_loc != loc_key:
            i += 1
            continue

        layer_qty = float(layer["qty"])
        layer_cost = float(layer["unit_cost"])

        take = min(layer_qty, remaining)
        pulls.append({"qty": round(take, 4), "unit_cost": round(layer_cost, 4),
                      "location": layer.get("location")})

        issued_value += take * layer_cost
        layer["qty"] = layer_qty - take
        remaining -= take

        if layer["qty"] <= 1e-9:
            prod["layers"].pop(i)  # don't increment i
        else:
            i += 1

    _sync_product_qty_and_avg_cost_from_layers(prod)
    eff_cost = (issued_value / qty_default) if qty_default > 0 else 0.0

    append_ledger_entry(
        "issue_from_location",
        {
            "product_id": prod.get("id"),
            "product_name": prod.get("product") or prod.get("name"),
            "location": location_name,
            "qty": round(qty_default, 4),
            "pulls": pulls,
            "effective_unit_cost": round(eff_cost, 4),
        },
    )

    return {
        "issued_qty": round(qty_default, 4),
        "issued_value": round(issued_value, 4),
        "pulls": pulls,
        "effective_unit_cost": round(eff_cost, 4),
    }

def _apply_package_rows_to_blend(blend_product, package_rows, location_id, location_name, finished_qty_gal, notes=None):
    """
    After a blend has been received into inventory as bulk (fifo_receive
    already ran for the full finished_qty_gal), optionally record that some
    of that same output is sitting in packages — mirroring the Repackage
    flow. This does NOT create additional inventory or deduct anything
    extra: the bulk FIFO total already reflects the full finished batch,
    and this just marks a portion of it as packaged so
    Unpackaged = total - packaged stays correct everywhere it's displayed.

    Returns (packaged_gal, package_summary_labels).
    """
    if not package_rows:
        return 0.0, []

    total_packaged_gal = 0.0
    for row in package_rows:
        vol_per = float(row.get("volume_per") or 0.0)
        pkg_unit = normalize_unit(row.get("unit") or "gal")
        qty = float(row.get("qty") or 0.0)
        total_packaged_gal += convert_to_product_default_unit(blend_product, qty * vol_per, pkg_unit)

    tolerance = max(0.05, float(finished_qty_gal) * 0.01)
    if total_packaged_gal > float(finished_qty_gal) + tolerance:
        raise BlendError(
            f"Packaged volume ({total_packaged_gal:.4f} GAL) exceeds the finished blend "
            f"quantity ({float(finished_qty_gal):.4f} GAL). Adjust the package rows."
        )

    pki_records = load_package_inventory()
    summary = []
    for row in package_rows:
        pki_records.append({
            "id":            generate_next_pki_id(pki_records),
            "product_id":    str(blend_product.get("id")),
            "package_id":    row["package_id"],
            "package_name":  row["package_name"],
            "quantity":      row["qty"],
            "volume_per":    row["volume_per"],
            "unit":          row["unit"],
            "total_volume":  round(row["qty"] * row["volume_per"], 4),
            "location_id":   location_id,
            "location_name": location_name,
            "received_at":   now_central_iso(),
            "type":          "blend",
            "notes":         notes,
        })
        summary.append(f"{row['qty']:g} x {row['package_name']}")
    save_package_inventory(pki_records)

    return round(total_packaged_gal, 4), summary


def execute_formula_blend(products: list, formula: dict, batch_qty: float, batch_unit: str, location: str | None = None,
                           consume_from_location_only: bool = False, location_id: str | None = None,
                           package_rows: list | None = None, notes: str | None = None):
    """
    Execute a stored formula:
    - Pull ingredients using FIFO layers (true cost)
    - Compute resulting blend cost/gal (from actual FIFO pulls)
    - Add finished blend into inventory as a new FIFO layer
    """

    if not formula:
        raise BlendError("Formula not found.")
    if not (location or "").strip():
        raise BlendError("Please select a location for the blend.")

    mode = (formula.get("mode") or "percent").lower()
    if mode != "percent":
        raise BlendError("Only percent-based formulas are supported for quick execute right now.")

    batch_unit = normalize_unit(batch_unit)
    if batch_unit not in ("gal", "lb"):
        raise BlendError("Batch unit must be GAL or LB.")

    try:
        batch_qty = float(batch_qty or 0.0)
    except Exception:
        batch_qty = 0.0
    if batch_qty <= 0:
        raise BlendError("Batch quantity must be > 0.")

    # Ensure products have layers (soft migration)
    migrate_products_to_layers(products)

    by_id = index_products_by_id(products)

    # Build component requirements from percents
    components = formula.get("components") or []
    if not components:
        raise BlendError("This formula has no components.")

    total_pct = sum(float(c.get("percent") or 0.0) for c in components)
    if abs(total_pct - 100.0) > 0.001:
        raise BlendError(f"Formula percents must sum to 100%. Current: {total_pct:.4f}%.")

    # Compute required quantities + total gallons + density (lb/gal)
    rows = []
    for c in components:
        pid = (c.get("product_id") or "").strip()
        pct = float(c.get("percent") or 0.0)
        if not pid or pct <= 0:
            continue

        prod = by_id.get(pid)
        if not prod:
            raise BlendError(f"Formula references unknown product id: {pid}")

        required_in_batch_unit = (pct / 100.0) * batch_qty
        req_in_prod_unit, req_unit_str, vol_gal = convert_required_to_product_unit(
            prod, required_in_batch_unit, batch_unit
        )
        if req_in_prod_unit is None:
            raise BlendError(
                f"Cannot convert requirement for '{prod.get('name')}' into its default unit. "
                f"Missing weight/package_size_gal?"
            )

        rows.append({
            "product": prod,
            "product_id": pid,
            "percent": pct,
            "required_qty_in_product_unit": float(req_in_prod_unit),
            "required_unit": req_unit_str,
            "vol_gal": float(vol_gal),
        })

    if not rows:
        raise BlendError("No valid component rows after parsing formula.")

    total_gal = sum(r["vol_gal"] for r in rows)
    if total_gal <= 0:
        raise BlendError("Total gallons computed as 0; cannot execute.")

    # weighted density (lb/gal) snapshot for the finished blend
    try:
        blend_lb_per_gal = float(compute_weighted_lb_per_gal(rows))
    except Exception:
        blend_lb_per_gal = None

    # ---- FIFO pull ingredients (true layer-based cost) ----
    pulls_for_rollback = []  # [(prod, pulls_list)]
    total_cost_value = 0.0

    try:
        for r in rows:
            prod = r["product"]
            qty_need = float(r["required_qty_in_product_unit"])

            if consume_from_location_only:
                issue_info = fifo_issue_from_location(prod, qty_need, location)
            else:
                issue_info = fifo_issue(prod, qty_need)  # updates prod layers + avg cost :contentReference[oaicite:3]{index=3}
            total_cost_value += float(issue_info["issued_value"] or 0.0)
            pulls_for_rollback.append((prod, issue_info.get("pulls") or []))
    except Exception as e:
        # rollback any partial pulls (put layers back)
        for prod, pulls in reversed(pulls_for_rollback):
            try:
                fifo_return(prod, pulls)
            except Exception:
                pass
        raise

    cost_per_gal = (total_cost_value / total_gal) if total_gal > 0 else 0.0
    cost_per_gal = round(float(cost_per_gal), 4)

    # ---- Create/update finished blend product ----
    blend_name = (formula.get("name") or "Blend").strip()
    blend_loc = location.strip()

    # store blends as GAL inventory (even if user entered LB)
    finished_qty_gal = float(total_gal)

    # find existing blend by name (case-insensitive)
    existing = next((p for p in products if (p.get("name") or "").strip().lower() == blend_name.lower()), None)

    now = now_central_iso()

    if existing:
        existing.setdefault("supplier", "Blend")
        existing["notes"] = existing.get("notes") or "Auto-generated blend"
        existing["location"] = blend_loc
        existing["last_updated"] = now

        # weight = lb/gal for display/conversions
        if blend_lb_per_gal:
            existing["weight"] = round(float(blend_lb_per_gal), 6)

        # add new FIFO layer at actual cost/gal
        fifo_receive(existing, finished_qty_gal, cost_per_gal, location=blend_loc)

        blend_product = existing
        created_new = False
    else:
        new_id = generate_next_product_id(products)
        blend_product = {
            "id": new_id,
            "name": blend_name,
            "phase": "liquid",
            "cas": None,
            "weight": round(float(blend_lb_per_gal), 6) if blend_lb_per_gal else None,
            "default_unit": "GAL",
            "unit_cost": cost_per_gal,
            "quantity": 0.0,
            "supplier": "Blend",
            "package_type": None,
            "package_size_gal": None,
            "location": blend_loc,
            "notes": "Auto-generated blend",
            "last_updated": now,
            "layers": [],
        }
        fifo_receive(blend_product, finished_qty_gal, cost_per_gal, location=blend_loc)
        products.append(blend_product)
        created_new = True

    # ---- Optionally record part of this finished batch as packaged ----
    # (does not touch bulk FIFO — see _apply_package_rows_to_blend)
    packaged_gal = 0.0
    package_summary = []
    if package_rows:
        packaged_gal, package_summary = _apply_package_rows_to_blend(
            blend_product, package_rows, location_id, blend_loc, finished_qty_gal, notes,
        )

    return {
        "blend_product": blend_product,
        "created_new": created_new,
        "total_gal": round(total_gal, 4),
        "total_cost_value": round(total_cost_value, 4),
        "cost_per_gal": cost_per_gal,
        "lb_per_gal": round(float(blend_lb_per_gal), 6) if blend_lb_per_gal else None,
        "packaged_gal": packaged_gal,
        "unpackaged_gal": round(max(0.0, float(finished_qty_gal) - packaged_gal), 4),
        "package_summary": package_summary,

        # ✅ add these so your “+ blend” row works
        "blend_name": blend_product.get("name"),
        "qty_added": round(float(finished_qty_gal), 4),
        "blend_new_qty": round(float(blend_product.get("quantity") or 0.0), 4),

        "components": [
            {
                "product_id": r["product_id"],
                "name": r["product"].get("name"),
                "percent": r["percent"],

                "qty_used": round(float(r["required_qty_in_product_unit"]), 4),
                "unit": r["required_unit"],
                "vol_gal": round(float(r["vol_gal"]), 4),

                # ✅ NEW: per-ingredient cost math
                # Assumption: product["unit_cost"] is $/GAL (which matches your blend_product layers)
                "unit_cost": round(float(r["product"].get("unit_cost") or 0.0), 4),
                "total_cost": round(float(r["vol_gal"]) * float(r["product"].get("unit_cost") or 0.0), 4),
                "cost_per_gal": round(
                    (float(r["vol_gal"]) * float(r["product"].get("unit_cost") or 0.0)) / float(total_gal),
                    4
                ) if float(total_gal) > 0 else 0.0,

                # ✅ NEW: remaining inventory AFTER the deduction already happened
                "new_qty": round(float(r["product"].get("quantity") or 0.0), 4),
            }
            for r in rows
        ],
    }

def _default_qty_to_gal(prod: dict, qty_default: float) -> float:
    """
    Convert a quantity expressed in the product's default_unit into gallons equivalent.
    Used for totaling batch gallons for absolute-mode blends.
    """
    u = normalize_unit(prod.get("default_unit"))
    qty_default = float(qty_default or 0.0)

    if u == "gal":
        return qty_default

    if u == "lb":
        w = prod.get("weight")  # lb/gal
        if not w:
            raise BlendError(f"Missing weight (lb/gal) for '{prod.get('name')}', needed to convert LB->GAL.")
        return qty_default / float(w)

    if u == "unit":
        ps = prod.get("package_size_gal")
        if not ps:
            raise BlendError(f"Missing package_size_gal for '{prod.get('name')}', needed to convert UNIT->GAL.")
        return qty_default * float(ps)

    # fallback
    raise BlendError(f"Unsupported default_unit '{u}' for '{prod.get('name')}'.")



# =====================================================================
# Tanks at a location (shared by Adjust Inventory and the Blend page)
# =====================================================================
# Tanks hold part of a product's *unpackaged* gallons at a location, so:
#   on hand at location = packaged + in tanks + loose (partial) gallons

def tank_rows_for_location(location_id, products_by_id=None) -> list:
    """Every active tank at a location with what's in it right now."""
    if not location_id:
        return []
    ledger = load_tank_ledger()
    products_by_id = products_by_id or {str(p.get("id")): p for p in load_products()}
    rows = []
    for t in get_tanks_for_location(load_tanks(), location_id):
        fill = round(max(0.0, get_tank_fill_gal(ledger, t.get("id"))), 4)
        cap = float(t.get("capacity_gal") or 0.0)
        pid = str(t.get("assigned_product_id")) if (fill > 1e-9 and t.get("assigned_product_id")) else None
        rows.append({
            "id": str(t.get("id")), "name": t.get("name") or str(t.get("id")),
            "capacity_gal": cap, "fill_gal": fill, "free_gal": round(max(0.0, cap - fill), 4),
            "product_id": pid,
            "product_name": (products_by_id.get(pid) or {}).get("name") if pid else None,
        })
    rows.sort(key=lambda r: r["name"].lower())
    return rows


def product_tank_gal(product_id, location_id) -> float:
    """Gallons of this product sitting in tanks at this location."""
    return round(sum(r["fill_gal"] for r in tank_rows_for_location(location_id)
                     if r["product_id"] == str(product_id)), 4)


def tank_receive_problem(tank_row, product_id, gal):
    """Why this tank can't take `gal` of this product (or None if it can)."""
    if not tank_row:
        return "That tank isn't at this location."
    if tank_row["product_id"] and tank_row["product_id"] != str(product_id):
        return (f"{tank_row['name']} already holds {tank_row['product_name'] or 'another product'}. "
                f"Empty it before putting a different product in.")
    if gal > tank_row["free_gal"] + 1e-6:
        return f"{tank_row['name']} only has room for {tank_row['free_gal']:g} more gal."
    return None


def tank_issue_problem(tank_row, product_id, gal):
    """Why `gal` of this product can't come out of this tank (or None if it can)."""
    if not tank_row:
        return "That tank isn't at this location."
    if tank_row["product_id"] != str(product_id):
        return f"{tank_row['name']} doesn't hold this product."
    if gal > tank_row["fill_gal"] + 1e-6:
        return f"{tank_row['name']} only has {tank_row['fill_gal']:g} gal in it."
    return None


# =====================================================================
# Blend from formula with package sourcing (mirrors the company Blend Log)
# =====================================================================
# For each ingredient the operator records where the gallons physically came
# from at the blend location:
#   - full packages of each type used (e.g. 2 x 330 Tote)
#   - gallons taken from partial / unpackaged stock
#   - one newly opened package + gallons poured out of it (the rest of that
#     package becomes partial stock automatically)
# Pulled must cover what the formula needs. The batch size never changes:
# anything pulled beyond the need is logged as overage / loss.

BLEND_TOLERANCE_GAL = 0.01


class SourcingError(Exception):
    """A blend can't run as entered. .errors holds one message per problem."""
    def __init__(self, message, errors=None):
        super().__init__(message)
        self.errors = errors or [message]


def _gal_to_default_qty(prod: dict, gal: float) -> float:
    """Gallons -> the product's own default unit (inverse of _default_qty_to_gal)."""
    u = normalize_unit(prod.get("default_unit"))
    gal = float(gal or 0.0)
    if u == "gal":
        return gal
    if u == "lb":
        w = prod.get("weight")
        if not w:
            raise SourcingError(f"'{prod.get('name')}' has no weight (lb/gal) set, so gallons can't be converted.")
        return gal * float(w)
    if u == "unit":
        ps = prod.get("package_size_gal")
        if not ps:
            raise SourcingError(f"'{prod.get('name')}' has no package size set, so gallons can't be converted.")
        return gal / float(ps)
    raise SourcingError(f"Unsupported unit '{u}' for '{prod.get('name')}'.")


def location_stock_for_product(prod: dict, location_id: str, location_name: str) -> dict:
    """What one product has on hand at one location, in gallons, split by package type."""
    _ensure_layers(prod)
    key = (location_name or "").strip().lower()
    bulk_default = sum(
        float(l.get("qty") or 0.0) for l in (prod.get("layers") or [])
        if (l.get("location") or prod.get("location") or "").strip().lower() == key
    )
    try:
        bulk_gal = _default_qty_to_gal(prod, bulk_default)
    except Exception:
        bulk_gal = 0.0

    packages = []
    packaged_gal = 0.0
    for pk in get_package_inventory_summary_for_location(prod.get("id"), location_id).values():
        qty = float(pk.get("quantity") or 0.0)
        vol_gal = package_volume_to_gallons(prod, float(pk.get("volume_per") or 0.0), pk.get("unit"))
        if qty <= 0 or vol_gal <= 0:
            continue
        packages.append({
            "package_id": str(pk.get("package_id")),
            "package_name": pk.get("package_name"),
            "volume_gal": round(vol_gal, 4),
            "quantity": int(round(qty)) if abs(qty - round(qty)) < 1e-9 else qty,
        })
        packaged_gal += qty * vol_gal

    tanks = [t for t in tank_rows_for_location(location_id) if t["product_id"] == str(prod.get("id"))]
    tank_gal = sum(t["fill_gal"] for t in tanks)
    return {
        "bulk_gal": round(bulk_gal, 4),
        "packages": packages,
        "tanks": [{"tank_id": t["id"], "name": t["name"], "fill_gal": t["fill_gal"]} for t in tanks],
        "tank_gal": round(tank_gal, 4),
        # loose / partial gallons = not in a package and not in a tank
        "unpackaged_gal": round(max(0.0, bulk_gal - packaged_gal - tank_gal), 4),
    }


def plan_formula_requirements(products: list, formula: dict, batch_qty: float, batch_unit: str,
                              allow_zero: bool = False) -> list:
    """Gallons each formula component needs for this batch.
    allow_zero=True lists the components with 0 needed (preview before a batch size is entered)."""
    if not formula:
        raise SourcingError("Formula not found.")
    if (formula.get("mode") or "percent").lower() != "percent":
        raise SourcingError("Only percent formulas can be executed.")
    batch_unit = normalize_unit(batch_unit)
    if batch_unit not in ("gal", "lb"):
        raise SourcingError("Batch unit must be GAL or LB.")
    try:
        batch_qty = float(batch_qty or 0.0)
    except Exception:
        batch_qty = 0.0
    if batch_qty < 0 or (batch_qty == 0 and not allow_zero):
        raise SourcingError("Batch quantity must be more than 0.")

    comps = formula.get("components") or []
    total_pct = sum(float(c.get("percent") or 0.0) for c in comps)
    if not comps:
        raise SourcingError("This formula has no components.")
    if abs(total_pct - 100.0) > 0.001:
        raise SourcingError(f"Formula percents must add up to 100% (they add up to {total_pct:.3f}%).")

    by_id = index_products_by_id(products)
    rows = []
    for c in comps:
        pid = str(c.get("product_id") or "").strip()
        pct = float(c.get("percent") or 0.0)
        if not pid or pct <= 0:
            continue
        prod = by_id.get(pid)
        if not prod:
            raise SourcingError(f"The formula uses a product that no longer exists (id {pid}).")
        req, unit_str, vol_gal = convert_required_to_product_unit(prod, (pct / 100.0) * batch_qty, batch_unit)
        if req is None:
            raise SourcingError(f"Can't convert the amount for '{prod.get('name')}'. Check its weight and unit.")
        rows.append({
            "product": prod, "product_id": pid, "name": prod.get("name"), "percent": pct,
            "needed_gal": round(float(vol_gal), 4),
            "needed_default_qty": float(req), "default_unit": unit_str,
        })
    if not rows:
        raise SourcingError("No usable components in this formula.")
    return rows


def _parse_sourcing(form, product_id: str) -> dict:
    """Read one component's sourcing inputs from the submitted form."""
    def num(name):
        raw = (form.get(name) or "").strip()
        if not raw:
            return 0.0
        try:
            v = float(raw)
        except ValueError:
            raise SourcingError("Amounts must be numbers.")
        if v < 0:
            raise SourcingError("Amounts can't be negative.")
        return v

    prefix = f"full__{product_id}__"
    full = {}
    for key in form.keys():
        if key.startswith(prefix):
            n = num(key)
            if n:
                if abs(n - round(n)) > 1e-9:
                    raise SourcingError("Full packages must be whole numbers.")
                full[key[len(prefix):]] = int(round(n))
    return {
        "full": full,
        "partial_gal": num(f"partial__{product_id}"),
        "open_package_id": (form.get(f"openpkg__{product_id}") or "").strip(),
        "open_gal": num(f"opengal__{product_id}"),
        "tank_id": (form.get(f"tank__{product_id}") or "").strip(),
        "tank_gal": num(f"tankgal__{product_id}"),
    }


def _parse_output_packages(form, total_gal: float):
    """'Package the finished blend' rows -> list of package rows, validated against the batch size."""
    pkg_by_id = {str(pk.get("id")): pk for pk in load_packages()}
    rows, packaged_gal = [], 0.0
    for pkg_id, raw in zip(form.getlist("out_package_id[]"), form.getlist("out_package_qty[]")):
        pkg_id, raw = (pkg_id or "").strip(), (raw or "").strip()
        if not pkg_id and not raw:
            continue
        pk = pkg_by_id.get(pkg_id)
        if not pk:
            raise SourcingError("Pick a package type for every packaging row.")
        try:
            n = float(raw)
        except ValueError:
            raise SourcingError("Package counts must be numbers.")
        if n <= 0 or abs(n - round(n)) > 1e-9:
            raise SourcingError("Package counts must be whole numbers above 0.")
        vol = float(pk.get("volume") or 0.0)
        unit = normalize_unit(pk.get("unit") or "gal")
        if unit != "gal" or vol <= 0:
            raise SourcingError(f"{pk.get('name')} isn't measured in gallons, so it can't be filled from a blend.")
        rows.append({"package_id": pkg_id, "package_name": pk.get("name"), "qty": int(round(n)),
                     "volume_per": vol, "unit": "gal"})
        packaged_gal += int(round(n)) * vol
    if packaged_gal > total_gal + BLEND_TOLERANCE_GAL:
        raise SourcingError(f"The packages hold {packaged_gal:g} GAL but the batch is only {total_gal:g} GAL.")
    return rows, round(packaged_gal, 4)


def execute_sourced_formula_blend(products, formula, batch_qty, batch_unit, location_id, location_name,
                                  form, notes=None, username=None, dry_run=False) -> dict:
    """With dry_run=True, only checks everything and changes nothing."""
    rows = plan_formula_requirements(products, formula, batch_qty, batch_unit)
    total_needed = sum(r["needed_gal"] for r in rows)
    out_rows, out_gal = _parse_output_packages(form, total_needed)
    loc_tanks = tank_rows_for_location(location_id, {str(p.get("id")): p for p in products})

    # ---------- 1. Validate every component before touching inventory ----------
    errors = []

    # Optional: send some of the finished blend into a tank
    out_tank = None
    out_tank_id = (form.get("out_tank_id") or "").strip()
    try:
        out_tank_gal = float((form.get("out_tank_gal") or "0").strip() or 0)
    except ValueError:
        out_tank_gal = -1
    if out_tank_id or out_tank_gal:
        trow = next((t for t in loc_tanks if t["id"] == out_tank_id), None)
        blend_name_lc = (formula.get("name") or "Blend").strip().lower()
        blend_pid = next((str(p.get("id")) for p in products
                          if (p.get("name") or "").strip().lower() == blend_name_lc), None)
        if not out_tank_id:
            errors.append("Finished blend: pick which tank it's going into.")
        elif out_tank_gal <= 0:
            errors.append("Finished blend: enter how many gallons go into the tank.")
        elif out_gal + out_tank_gal > total_needed + BLEND_TOLERANCE_GAL:
            errors.append(f"Finished blend: packages plus tank ({out_gal + out_tank_gal:g} gal) "
                          f"is more than the batch ({total_needed:g} gal).")
        else:
            problem = tank_receive_problem(trow, blend_pid or "__new__", out_tank_gal)
            if problem:
                errors.append(f"Finished blend: {problem}")
            else:
                out_tank = {"tank_id": trow["id"], "name": trow["name"], "gal": round(out_tank_gal, 4)}
    for r in rows:
        prod = r["product"]
        name = r["name"]
        stock = location_stock_for_product(prod, location_id, location_name)
        pkgs = {p["package_id"]: p for p in stock["packages"]}
        try:
            src = _parse_sourcing(form, r["product_id"])
        except SourcingError as e:
            errors.append(f"{name}: {e}")
            continue

        used_by_pkg = {}
        full_rows, full_gal = [], 0.0
        for pkg_id, n in src["full"].items():
            pk = pkgs.get(pkg_id)
            if not pk:
                errors.append(f"{name}: there are no full packages of that type at {location_name}.")
                continue
            used_by_pkg[pkg_id] = used_by_pkg.get(pkg_id, 0) + n
            full_rows.append({"package_id": pkg_id, "package_name": pk["package_name"], "qty": n,
                              "volume_per": pk["volume_gal"], "unit": "gal"})
            full_gal += n * pk["volume_gal"]

        opened = None
        if src["open_package_id"] or src["open_gal"]:
            pk = pkgs.get(src["open_package_id"])
            if not pk:
                errors.append(f"{name}: pick which package type was opened.")
            elif src["open_gal"] <= 0:
                errors.append(f"{name}: enter how many gallons came out of the opened {pk['package_name']}.")
            elif src["open_gal"] > pk["volume_gal"] + BLEND_TOLERANCE_GAL:
                errors.append(f"{name}: can't pour {src['open_gal']:g} gal out of a {pk['package_name']} "
                              f"({pk['volume_gal']:g} gal). Count it as a full package instead.")
            else:
                used_by_pkg[pk["package_id"]] = used_by_pkg.get(pk["package_id"], 0) + 1
                opened = {"package_id": pk["package_id"], "package_name": pk["package_name"],
                          "volume_gal": pk["volume_gal"], "gal_out": round(src["open_gal"], 4)}

        for pkg_id, n in used_by_pkg.items():
            have = pkgs[pkg_id]["quantity"] if pkg_id in pkgs else 0
            if n > have:
                errors.append(f"{name}: needs {n} x {pkgs[pkg_id]['package_name']} but only {have:g} "
                              f"on hand at {location_name}.")

        if src["partial_gal"] > stock["unpackaged_gal"] + BLEND_TOLERANCE_GAL:
            errors.append(f"{name}: only {stock['unpackaged_gal']:g} gal of partial stock at {location_name}.")

        tank_pull = None
        if src["tank_id"] or src["tank_gal"]:
            trow = next((t for t in loc_tanks if t["id"] == src["tank_id"]), None)
            if not src["tank_id"]:
                errors.append(f"{name}: pick which tank it came out of.")
            elif src["tank_gal"] <= 0:
                errors.append(f"{name}: enter how many gallons came out of the tank.")
            else:
                problem = tank_issue_problem(trow, r["product_id"], src["tank_gal"])
                if problem:
                    errors.append(f"{name}: {problem}")
                else:
                    tank_pull = {"tank_id": trow["id"], "name": trow["name"], "gal": round(src["tank_gal"], 4)}

        pulled = (full_gal + src["partial_gal"] + (opened["gal_out"] if opened else 0.0)
                  + (tank_pull["gal"] if tank_pull else 0.0))
        errors_before = len(errors)
        if pulled + BLEND_TOLERANCE_GAL < r["needed_gal"] and not any(e.startswith(name + ":") for e in errors):
            errors.append(f"{name}: pulled {pulled:g} gal but the formula needs {r['needed_gal']:g} gal.")
        # Only mention the overall total if nothing more specific was already said about this ingredient
        if pulled > stock["bulk_gal"] + BLEND_TOLERANCE_GAL and not any(
                e.startswith(name + ":") for e in errors):
            errors.append(f"{name}: only {stock['bulk_gal']:g} gal on hand at {location_name}.")

        r.update({
            "full_rows": full_rows, "partial_gal": round(src["partial_gal"], 4), "opened": opened,
            "tank_pull": tank_pull,
            "pulled_gal": round(pulled, 4), "overage_gal": round(max(0.0, pulled - r["needed_gal"]), 4),
        })

    if errors:
        raise SourcingError(" ".join(errors), errors)
    if dry_run:
        return {"ok": True}

    # ---------- 2. Pull from FIFO at this location ----------
    pulls_for_rollback = []
    blend_cost = 0.0
    overage_cost_total = 0.0
    try:
        for r in rows:
            prod = r["product"]
            used = fifo_issue_from_location(prod, r["needed_default_qty"], location_name)
            pulls_for_rollback.append((prod, used.get("pulls") or []))
            r["cost"] = round(float(used["issued_value"] or 0.0), 4)
            blend_cost += r["cost"]
            r["overage_cost"] = 0.0
            if r["overage_gal"] > 0:
                extra = fifo_issue_from_location(prod, _gal_to_default_qty(prod, r["overage_gal"]), location_name)
                pulls_for_rollback.append((prod, extra.get("pulls") or []))
                r["overage_cost"] = round(float(extra["issued_value"] or 0.0), 4)
                overage_cost_total += r["overage_cost"]
    except Exception:
        for prod, pulls in reversed(pulls_for_rollback):
            try:
                fifo_return(prod, pulls)
            except Exception:
                pass
        raise

    # ---------- 3. Update package counts (partial leftovers fall into unpackaged) ----------
    for r in rows:
        pid = r["product_id"]
        if r["full_rows"]:
            deduct_package_inventory(pid, r["full_rows"], location_id, location_name,
                                     notes or f"Blend: {formula.get('name')}", ref_type="blend_full")
        if r["opened"]:
            o = r["opened"]
            deduct_package_inventory(pid, [{"package_id": o["package_id"], "package_name": o["package_name"],
                                            "qty": 1, "volume_per": o["volume_gal"], "unit": "gal"}],
                                     location_id, location_name,
                                     f"Opened for blend {formula.get('name')}: {o['gal_out']:g} gal out",
                                     ref_type="blend_opened")

    for r in rows:
        if r["tank_pull"]:
            apply_tank_issue(r["tank_pull"]["tank_id"], r["product"], r["tank_pull"]["gal"], "gal",
                             source="blend", ref=formula.get("name"),
                             notes=f"Pulled for blend {formula.get('name')}")

    # ---------- 4. Receive the finished blend at the same location ----------
    total_gal = sum(r["needed_gal"] for r in rows)
    try:
        lb_per_gal = float(compute_weighted_lb_per_gal(
            [{"product": r["product"], "vol_gal": r["needed_gal"],
              "required_qty_in_product_unit": r["needed_default_qty"]} for r in rows]))
    except Exception:
        lb_per_gal = None
    cost_per_gal = round(blend_cost / total_gal, 4) if total_gal > 0 else 0.0

    blend_name = (formula.get("name") or "Blend").strip()
    existing = next((p for p in products if (p.get("name") or "").strip().lower() == blend_name.lower()), None)
    now = now_central_iso()
    if existing:
        blend_product = existing
        existing["last_updated"] = now
        if lb_per_gal:
            existing["weight"] = round(lb_per_gal, 6)
    else:
        blend_product = {
            "id": generate_next_product_id(products), "name": blend_name, "phase": "liquid", "cas": None,
            "weight": round(lb_per_gal, 6) if lb_per_gal else None, "default_unit": "GAL",
            "unit_cost": cost_per_gal, "quantity": 0.0, "supplier": "Blend", "package_type": None,
            "package_size_gal": None, "location_id": location_id, "location": location_name,
            "notes": "Auto-generated blend", "last_updated": now, "layers": [],
        }
        products.append(blend_product)
    fifo_receive(blend_product, _gal_to_default_qty(blend_product, total_gal), cost_per_gal, location=location_name)

    # Record the part of the batch that went straight into packages (the rest stays unpackaged)
    if out_rows:
        _apply_package_rows_to_blend(blend_product, out_rows, location_id, location_name, total_gal,
                                     notes or f"Blend {blend_name}")
    if out_tank:
        apply_tank_receive(out_tank["tank_id"], blend_product, out_tank["gal"], "gal",
                           source="blend", ref=blend_name, notes=f"Finished blend {blend_name}")

    # ---------- 5. Blend Log entry ----------
    log = load_blends()
    next_no = max([int(b.get("number") or 0) for b in log] + [0]) + 1
    entry = {
        "id": str(uuid.uuid4()),
        "number": next_no,
        "date": now,
        "location_id": location_id,
        "location": location_name,
        "formula_id": formula.get("id"),
        "blend": blend_name,
        "blend_product_id": blend_product.get("id"),
        "batch_qty": float(batch_qty),
        "batch_unit": normalize_unit(batch_unit),
        "total_gal": round(total_gal, 4),
        "cost_per_gal": cost_per_gal,
        "total_cost": round(blend_cost, 4),
        "overage_cost": round(overage_cost_total, 4),
        "packaged": [{"package_name": o["package_name"], "qty": o["qty"]} for o in out_rows],
        "packaged_gal": out_gal,
        "out_tank": ({"name": out_tank["name"], "gal": out_tank["gal"]} if out_tank else None),
        "unpackaged_gal": round(max(0.0, total_gal - out_gal - (out_tank["gal"] if out_tank else 0)), 4),
        "notes": notes,
        "by": username,
        "components": [{
            "product_id": r["product_id"], "name": r["name"], "percent": r["percent"],
            "needed_gal": r["needed_gal"],
            "full": [{"package_name": f["package_name"], "qty": f["qty"]} for f in r["full_rows"]],
            "partial_gal": r["partial_gal"],
            "opened": ({"package_name": r["opened"]["package_name"], "gal_out": r["opened"]["gal_out"]}
                       if r["opened"] else None),
            "tank": ({"name": r["tank_pull"]["name"], "gal": r["tank_pull"]["gal"]} if r["tank_pull"] else None),
            "pulled_gal": r["pulled_gal"], "overage_gal": r["overage_gal"],
            "cost": r["cost"], "overage_cost": r["overage_cost"],
        } for r in rows],
    }
    log.append(entry)
    save_blends(log)
    append_ledger_entry("blend_executed", {
        "number": next_no, "blend": blend_name, "location": location_name, "total_gal": entry["total_gal"],
        "overage_gal": round(sum(r["overage_gal"] for r in rows), 4), "by": username,
    })
    entry["blend_new_qty"] = round(float(blend_product.get("quantity") or 0.0), 4)
    return entry

def execute_builder_blend(products: list, name: str, target_qty: float, target_unit: str, mode: str, components: list, location: str | None = None,
                           consume_from_location_only: bool = False, location_id: str | None = None,
                           package_rows: list | None = None, notes: str | None = None):
    """
    Execute a one-off blend coming straight from the Blend Builder payload:
    - consumes ingredient inventory via FIFO layers
    - computes true cost per gallon based on actual pulls
    - receives finished blend as a FIFO layer in inventory
    Supports:
      - percent mode (target_qty + target_unit)
      - absolute mode (each component has qty + qty_unit)
    """
    name = (name or "").strip()
    if not name:
        raise BlendError("Blend name is required.")

    mode = (mode or "percent").lower()
    target_unit = normalize_unit(target_unit)
    location = (location or "").strip()
    if not location:
        raise BlendError("Please select a location for the blend.")

    try:
        target_qty = float(target_qty or 0.0)
    except Exception:
        target_qty = 0.0
    if target_qty <= 0:
        raise BlendError("Target quantity must be > 0.")

    if target_unit not in ("gal", "lb"):
        raise BlendError("Target unit must be GAL or LB.")

    if not components:
        raise BlendError("Add at least one ingredient.")

    # Ensure FIFO layers exist
    migrate_products_to_layers(products)
    by_id = index_products_by_id(products)

    # --- Build a normalized "rows" list with:
    # product, qty_need_in_default_unit, qty_used_display, unit_display, vol_gal
    rows = []

    if mode == "percent":
        total_pct = sum(float(c.get("percent") or 0.0) for c in components)
        if abs(total_pct - 100.0) > 0.001:
            raise BlendError(f"Percentages must sum to 100%. Current: {total_pct:.4f}%.")

        for c in components:
            pid = (c.get("product_id") or "").strip()
            pct = float(c.get("percent") or 0.0)
            if not pid or pct <= 0:
                continue

            prod = by_id.get(pid)
            if not prod:
                raise BlendError(f"Unknown product id: {pid}")

            required_in_batch_unit = (pct / 100.0) * target_qty
            qty_default, unit_str, vol_gal = convert_required_to_product_unit(prod, required_in_batch_unit, target_unit)

            if qty_default is None:
                raise BlendError(
                    f"Cannot convert requirement for '{prod.get('name')}' into its default unit. "
                    f"Missing weight/package_size_gal?"
                )

            rows.append({
                "product": prod,
                "qty_default": float(qty_default),
                "qty_used_display": float(required_in_batch_unit),
                "unit_display": target_unit.upper(),
                "vol_gal": float(vol_gal),
            })

    elif mode == "absolute":
        # Each component specifies qty + qty_unit; we convert that to product default unit for FIFO issue
        for c in components:
            pid = (c.get("product_id") or "").strip()
            if not pid:
                continue

            prod = by_id.get(pid)
            if not prod:
                raise BlendError(f"Unknown product id: {pid}")

            try:
                qty_in = float(c.get("qty") or 0.0)
            except Exception:
                qty_in = 0.0
            if qty_in <= 0:
                continue

            qty_unit = normalize_unit((c.get("qty_unit") or "gal").lower())
            if qty_unit not in ("gal", "lb", "unit"):
                raise BlendError("qty_unit must be GAL, LB, or UNIT in absolute mode.")

            # convert input qty to product default unit for FIFO issuing
            qty_default = convert_to_product_default_unit(prod, qty_in, qty_unit)

            # compute gallons equivalent for totals
            vol_gal = _default_qty_to_gal(prod, qty_default)

            rows.append({
                "product": prod,
                "qty_default": float(qty_default),
                "qty_used_display": float(qty_in),
                "unit_display": qty_unit.upper(),
                "vol_gal": float(vol_gal),
            })
    else:
        raise BlendError("Mode must be 'percent' or 'absolute'.")

    if not rows:
        raise BlendError("No valid ingredient rows after parsing.")

    total_gal = sum(r["vol_gal"] for r in rows)
    if total_gal <= 0:
        raise BlendError("Total gallons computed as 0; cannot execute.")

    # weighted density snapshot for blend (lb/gal)
    try:
        blend_lb_per_gal = float(compute_weighted_lb_per_gal(
            [{"product": r["product"], "vol_gal": r["vol_gal"]} for r in rows]
        ))
    except Exception:
        blend_lb_per_gal = None

    # --- FIFO pull ingredients (rollback-safe) ---
    pulls_for_rollback = []  # [(prod, pulls_list)]
    total_cost_value = 0.0
    components_used = []

    try:
        for r in rows:
            prod = r["product"]
            qty_need_default = float(r["qty_default"])

            if consume_from_location_only:
                issue_info = fifo_issue_from_location(prod, qty_need_default, location)
            else:
                issue_info = fifo_issue(prod, qty_need_default)  # pulls from FIFO layers (true cost)
            total_cost_value += float(issue_info.get("issued_value") or 0.0)
            pulls_for_rollback.append((prod, issue_info.get("pulls") or []))

            components_used.append({
                "id": prod.get("id"),
                "name": prod.get("name"),
                "qty_used": round(float(r["qty_used_display"]), 4),
                "unit": r["unit_display"],
            })

    except Exception as e:
        # rollback any partial pulls
        for prod, pulls in reversed(pulls_for_rollback):
            try:
                fifo_return(prod, pulls)
            except Exception:
                pass
        raise

    cost_per_gal = (total_cost_value / total_gal) if total_gal > 0 else 0.0
    cost_per_gal = round(float(cost_per_gal), 4)

    # --- Create/update finished blend product + receive layer ---
    blend_name = name
    blend_loc = location
    finished_qty_gal = float(total_gal)

    existing = next((p for p in products if (p.get("name") or "").strip().lower() == blend_name.lower()), None)
    now = now_central_iso()

    if existing:
        existing.setdefault("supplier", "Blend")
        existing["notes"] = existing.get("notes") or "Auto-generated blend"
        existing["location"] = blend_loc
        existing["last_updated"] = now
        if blend_lb_per_gal:
            existing["weight"] = round(float(blend_lb_per_gal), 6)

        fifo_receive(existing, finished_qty_gal, cost_per_gal, location=blend_loc)
        blend_product = existing
    else:
        blend_product = {
            "id": str(uuid.uuid4()),
            "name": blend_name,
            "supplier": "Blend",
            "default_unit": "gal",
            "location": blend_loc,
            "weight": round(float(blend_lb_per_gal), 6) if blend_lb_per_gal else None,
            "notes": "Auto-generated blend",
            "created_at": now,
            "last_updated": now,
            "layers": [],
            "quantity": 0.0,
            "cost": 0.0,
        }
        products.append(blend_product)
        fifo_receive(blend_product, finished_qty_gal, cost_per_gal, location=blend_loc)

    # ---- Optionally record part of this finished batch as packaged ----
    # (does not touch bulk FIFO — see _apply_package_rows_to_blend)
    packaged_gal = 0.0
    package_summary = []
    if package_rows:
        packaged_gal, package_summary = _apply_package_rows_to_blend(
            blend_product, package_rows, location_id, blend_loc, finished_qty_gal, notes,
        )

    return {
        "blend_name": blend_name,
        "total_gal": round(float(total_gal), 4),
        "total_cost_value": round(float(total_cost_value), 4),
        "cost_per_gal": cost_per_gal,
        "blend_lb_per_gal": round(float(blend_lb_per_gal), 6) if blend_lb_per_gal else None,
        "blend_product": blend_product,
        "components_used": components_used,
        "packaged_gal": packaged_gal,
        "unpackaged_gal": round(max(0.0, float(finished_qty_gal) - packaged_gal), 4),
        "package_summary": package_summary,
    }

def migrate_products_to_layers(products: list) -> bool:
    """
    Soft migration:
    - If a product has no layers, create one layer from quantity & unit_cost.
    - No 'ref', no 'migration' marker.
    """
    changed = False
    for p in products:
        if not isinstance(p, dict):
            continue

        layers = p.get("layers")
        if isinstance(layers, list) and len(layers) > 0:
            _sync_product_qty_and_avg_cost_from_layers(p)
            continue

        try:
            q = float(p.get("quantity") or 0.0)
        except Exception:
            q = 0.0
        try:
            c = float(p.get("unit_cost") or 0.0)
        except Exception:
            c = 0.0

        base_loc = (p.get("location") or "UNASSIGNED").strip() or "UNASSIGNED"

        p["layers"] = []
        if q > 0:
            p["layers"].append(
                {
                    "qty": round(q, 4),
                    "unit": normalize_unit(p.get("default_unit")),
                    "unit_cost": round(c, 4),
                    "datetime": p.get("last_updated") or now_central_iso(),
                    "location": base_loc,
                }
            )

        _sync_product_qty_and_avg_cost_from_layers(p)
        changed = True

    return changed



# -------------------------
# Conversions to product default unit (supports phase rules)
# -------------------------
def convert_to_product_default_unit(product, qty, from_unit):
    default_unit = normalize_unit(product.get("default_unit"))
    from_unit = normalize_unit(from_unit)
    qty = float(qty)
    phase = (product.get("phase") or "").strip().lower() or "liquid"

    if phase == "solid":
        if default_unit == "lb":
            if from_unit != "lb":
                raise ValueError("For solid products tracked in pounds, enter quantity in lb.")
            return qty
        if default_unit == "unit":
            if from_unit != "unit":
                raise ValueError("For solid products tracked in units, enter quantity in unit.")
            return qty
        raise ValueError("Solid products must use default unit 'lb' or 'unit'.")

    # liquid
    if default_unit == from_unit:
        return qty

    w = product.get("weight")  # lb/gal
    pkg = product.get("package_size_gal")  # gal per unit

    def gal_to_lb(g):
        if not (w and float(w) > 0):
            raise ValueError("Missing weight (lb/gal) for conversion.")
        return float(g) * float(w)

    def lb_to_gal(pounds):
        if not (w and float(w) > 0):
            raise ValueError("Missing weight (lb/gal) for conversion.")
        return float(pounds) / float(w)

    def unit_to_gal(units):
        if not (pkg and float(pkg) > 0):
            raise ValueError("Missing package_size_gal for conversion from unit.")
        return float(units) * float(pkg)

    def gal_to_unit(gallons):
        if not (pkg and float(pkg) > 0):
            raise ValueError("Missing package_size_gal for conversion to unit.")
        return float(gallons) / float(pkg)

    # from_unit -> gal
    if from_unit == "gal":
        gal = qty
    elif from_unit == "lb":
        gal = lb_to_gal(qty)
    elif from_unit == "unit":
        gal = unit_to_gal(qty)
    else:
        raise ValueError("Unit must be 'gal', 'lb', or 'unit'.")

    # gal -> default_unit
    if default_unit == "gal":
        return gal
    if default_unit == "lb":
        return gal_to_lb(gal)
    if default_unit == "unit":
        return gal_to_unit(gal)

    raise ValueError("Unsupported default_unit on product.")


# -------------------------
# Reorder Alerts compute
# -------------------------
ALERT_WARNING_RATIO = 1.15  # within 15% above the reorder point = "Warning"


def compute_reorder_alerts_with_status():
    """
    One row per reorder alert. Math is done in the product's default unit;
    display_* fields are in the unit the alert was entered in (e.g. LB), so
    the page shows the numbers the way the person typed them.
    Status: critical = below the reorder point, warning = within 15% above it,
    ok = comfortably above, invalid = the alert can't be evaluated.
    """
    products = load_products()
    alerts = load_alerts()
    prod_by_id = {p["id"]: p for p in products if p.get("id")}

    rows = []
    for a in alerts:
        pid = a.get("product_id")
        prod = prod_by_id.get(pid)
        if not prod:
            continue  # product was deleted; its alert is ignored
        thr_val = float(a.get("threshold_value") or 0.0)
        thr_unit = normalize_unit(a.get("threshold_unit") or prod.get("default_unit"))
        default_unit = normalize_unit(prod.get("default_unit"))
        on_hand = float(prod.get("quantity") or 0.0)

        row = {
            "product_id": pid, "name": prod.get("name"), "default_unit": default_unit,
            "on_hand": on_hand, "threshold": None, "ratio": None, "deficit": None,
            "display_unit": thr_unit, "display_threshold": thr_val, "display_on_hand": None,
            "display_deficit": None, "status": "invalid", "problem": None,
        }
        try:
            thr_in_default = float(convert_to_product_default_unit(prod, thr_val, thr_unit))
            per_display_unit = float(convert_to_product_default_unit(prod, 1.0, thr_unit))
        except Exception:
            row["problem"] = f"Can't convert {thr_unit.upper()} for this product. Set its weight or use {default_unit.upper()}."
            rows.append(row)
            continue
        if thr_in_default <= 0:
            row["problem"] = "No reorder point set."
            rows.append(row)
            continue

        ratio = on_hand / thr_in_default
        deficit = max(0.0, thr_in_default - on_hand)
        row.update({
            "threshold": thr_in_default, "ratio": ratio, "deficit": deficit,
            "display_on_hand": on_hand / per_display_unit if per_display_unit else None,
            "display_deficit": deficit / per_display_unit if per_display_unit else None,
            "status": "critical" if ratio < 1.0 else ("warning" if ratio < ALERT_WARNING_RATIO else "ok"),
        })
        rows.append(row)

    rows.sort(key=lambda r: ({"critical": 0, "warning": 1, "invalid": 2, "ok": 3}[r["status"]], r["ratio"] or 0))
    # Dashboard list: only products that are actually low or getting close
    top5 = [r for r in rows if r["status"] in ("critical", "warning")][:5]
    return rows, top5


def count_triggered_alerts():
    rows, _ = compute_reorder_alerts_with_status()
    triggered = sum(1 for r in rows if (r.get("ratio") is not None) and (r["ratio"] < 1.0))
    return triggered, len(rows)


# -------------------------
# Blend helpers & math
# -------------------------
class BlendError(Exception):
    pass


def _need_weight(p, context):
    w = p.get("weight")
    if w is None or float(w) <= 0:
        raise BlendError(f"Product '{p.get('name')}' is missing a valid lb/gal for {context}.")
    return float(w)


def index_products_by_id(products):
    return {p.get("id"): p for p in products if p.get("id")}


def vol_gal_of_component(product, qty, qty_unit):
    qty_unit = normalize_unit(qty_unit)
    pkg_gal = product.get("package_size_gal")

    if qty_unit == "gal":
        return float(qty)
    if qty_unit == "lb":
        w = _need_weight(product, "lb→gal conversion")
        return to_gallons(w, float(qty))
    if qty_unit == "unit":
        if pkg_gal and float(pkg_gal) > 0:
            return float(qty) * float(pkg_gal)
        raise BlendError(f"Cannot convert UNIT to gallons for '{product.get('name')}' (missing package_size_gal).")

    raise BlendError("qty_unit must be 'gal','lb', or 'unit'.")


def cost_for_component(product, required_qty_in_product_unit):
    if required_qty_in_product_unit is None:
        return 0.0
    unit_cost = float(product.get("unit_cost") or 0.0)
    return unit_cost * float(required_qty_in_product_unit)


def compute_weighted_lb_per_gal(components_rows):
    total_gal = sum(r["vol_gal"] for r in components_rows)
    if total_gal <= 0:
        return 0.0
    total_lb = 0.0
    for r in components_rows:
        w = _need_weight(r["product"], "blend density computation")
        total_lb += w * r["vol_gal"]
    return total_lb / total_gal


def compute_weighted_unit_cost_per_gal(components_rows):
    total_gal = sum(r["vol_gal"] for r in components_rows)
    if total_gal <= 0:
        return 0.0
    total_cost = 0.0
    for r in components_rows:
        total_cost += cost_for_component(r["product"], r["required_qty_in_product_unit"])
    return total_cost / total_gal


def convert_required_to_product_unit(product, required_in_batch_unit, batch_unit):
    default_unit = normalize_unit(product.get("default_unit"))
    batch_unit = normalize_unit(batch_unit)
    pkg_gal = product.get("package_size_gal")

    if batch_unit == "gal":
        req_gal = float(required_in_batch_unit)
        if default_unit == "gal":
            return req_gal, "gal", req_gal
        if default_unit == "lb":
            w = _need_weight(product, "gal→lb conversion")
            return to_pounds(w, req_gal), "lb", req_gal
        if default_unit == "unit":
            if pkg_gal and float(pkg_gal) > 0:
                return (req_gal / float(pkg_gal)), "unit", req_gal
            return None, "unit", req_gal

    elif batch_unit == "lb":
        req_lb = float(required_in_batch_unit)
        if default_unit == "lb":
            # if weight exists, we can compute reference gallons
            try:
                w = _need_weight(product, "lb→gal reference")
                ref_gal = to_gallons(w, req_lb)
            except BlendError:
                ref_gal = 0.0
            return req_lb, "lb", float(ref_gal)

        if default_unit == "gal":
            w = _need_weight(product, "lb→gal conversion")
            gal = to_gallons(w, req_lb)
            return gal, "gal", gal

        if default_unit == "unit":
            w = product.get("weight")
            if not (w and float(w) > 0):
                return None, "unit", 0.0
            ref_gal = to_gallons(float(w), req_lb)
            if pkg_gal and float(pkg_gal) > 0:
                return (ref_gal / float(pkg_gal)), "unit", ref_gal
            return None, "unit", ref_gal

    raise BlendError(f"Unsupported conversion for batch_unit '{batch_unit}'.")


def build_blend(products, name, target_qty, target_unit, mode, components, location=None):
    target_unit = normalize_unit(target_unit)
    if target_unit not in ("gal", "lb"):
        raise BlendError("Target unit must be GAL or LB.")
    if float(target_qty) <= 0:
        raise BlendError("Target quantity must be > 0.")
    if mode not in ("percent", "absolute"):
        raise BlendError("Mode must be 'percent' or 'absolute'.")

    by_id = index_products_by_id(products)
    rows = []

    if mode == "percent":
        total_pct = sum(float(c.get("percent", 0) or 0) for c in components)
        if abs(total_pct - 100.0) > 0.001:
            raise BlendError(f"Percentages must sum to 100 (got {total_pct:.3f}).")

        for c in components:
            pid = c.get("product_id")
            pct = float(c.get("percent", 0) or 0)
            if pct <= 0:
                continue
            prod = by_id.get(pid)
            if not prod:
                raise BlendError(f"Product id '{pid}' not found.")

            required_in_batch_unit = (pct / 100.0) * float(target_qty)
            q_prod, unit_str, vol_gal = convert_required_to_product_unit(prod, required_in_batch_unit, target_unit)
            rows.append(
                {
                    "product": prod,
                    "required_in_batch_unit": required_in_batch_unit,
                    "qty_unit_batch": target_unit,
                    "required_qty_in_product_unit": q_prod,
                    "product_unit": unit_str,
                    "vol_gal": float(vol_gal),
                }
            )

    else:
        normalized_rows = []
        for c in components:
            pid = c.get("product_id")
            qty = float(c.get("qty", 0) or 0)
            qty_unit = normalize_unit(c.get("qty_unit") or "")
            if qty <= 0:
                continue
            prod = by_id.get(pid)
            if not prod:
                raise BlendError(f"Product id '{pid}' not found.")

            if target_unit == "gal":
                required_in_batch_unit = vol_gal_of_component(prod, qty, qty_unit)
            else:
                # target lb
                if qty_unit == "lb":
                    required_in_batch_unit = qty
                elif qty_unit == "gal":
                    w = _need_weight(prod, "gal→lb (absolute mode)")
                    required_in_batch_unit = to_pounds(w, qty)
                elif qty_unit == "unit":
                    pkg = prod.get("package_size_gal")
                    if not (pkg and float(pkg) > 0):
                        raise BlendError(f"Cannot convert UNIT for '{prod.get('name')}' (missing package_size_gal).")
                    gal = qty * float(pkg)
                    w = _need_weight(prod, "gal→lb (absolute mode)")
                    required_in_batch_unit = to_pounds(w, gal)
                else:
                    raise BlendError("qty_unit must be 'gal','lb', or 'unit'.")

            q_prod, unit_str, vol_gal = convert_required_to_product_unit(prod, required_in_batch_unit, target_unit)
            normalized_rows.append(
                {
                    "product": prod,
                    "required_in_batch_unit": required_in_batch_unit,
                    "qty_unit_batch": target_unit,
                    "required_qty_in_product_unit": q_prod,
                    "product_unit": unit_str,
                    "vol_gal": float(vol_gal),
                }
            )

        normalized_total = sum(r["required_in_batch_unit"] for r in normalized_rows)
        if abs(normalized_total - float(target_qty)) > 1e-6:
            raise BlendError(
                f"Absolute quantities must sum to target {target_qty} {target_unit} "
                f"(got {normalized_total:.4f} {target_unit})."
            )
        rows = normalized_rows

    # inventory validation
    for r in rows:
        on_hand = float(r["product"].get("quantity") or 0.0)
        req = r["required_qty_in_product_unit"]
        if req is None:
            raise BlendError(
                f"Cannot compute required units for '{r['product'].get('name')}'. "
                "Add package_size_gal (for UNIT products) and/or weight (lb/gal)."
            )
        if float(req) > on_hand + 1e-9:
            raise BlendError(
                f"Not enough '{r['product'].get('name')}' in inventory. "
                f"Need {req:.4f} {r['product_unit']}, on hand {on_hand:.4f}."
            )

    blend_lb_per_gal = compute_weighted_lb_per_gal(rows)
    cost_per_gal = compute_weighted_unit_cost_per_gal(rows)

    # determine final blend qty in gallons
    if target_unit == "gal":
        new_quantity = float(target_qty)
        new_default_unit = "gal"
    else:
        if blend_lb_per_gal <= 0:
            raise BlendError("Computed blend lb/gal is invalid (<= 0).")
        new_quantity = to_gallons(blend_lb_per_gal, float(target_qty))
        new_default_unit = "gal"

    # deduct inventory
    for r in rows:
        req = float(r["required_qty_in_product_unit"])
        r["product"]["quantity"] = max(0.0, float(r["product"].get("quantity") or 0.0) - req)

    new_product = {
        "id": generate_next_product_id(products),
        "name": name,
        "phase": "liquid",
        "cas": None,
        "weight": float(blend_lb_per_gal),
        "default_unit": new_default_unit,
        "unit_cost": float(cost_per_gal),
        "quantity": float(new_quantity),
        "supplier": "Blend",
        "package_type": None,
        "package_size_gal": None,
        "location": location,
        "notes": "Auto-generated blend",
        "last_updated": now_central_iso(),
    }
    products.append(new_product)

    return {
        "new_product": new_product,
        "used_components": [
            {
                "id": r["product"]["id"],
                "name": r["product"]["name"],
                "required_qty": r["required_qty_in_product_unit"],
                "required_unit": r["product_unit"],
                "vol_gal": r["vol_gal"],
            }
            for r in rows
        ],
        "blend_lb_per_gal": blend_lb_per_gal,
        "cost_per_gal": cost_per_gal,
    }


# -------------------------
# Staging (reserve/release/void) using FIFO
# -------------------------
class StagingError(Exception):
    pass


def stage_create(products, product_id, qty, unit, customer=None, reason=None, scheduled_date=None, notes=None, package_breakdown=None,
                 location_id=None, location_name=None, tanks=None):
    qty = float(qty)
    if qty <= 0:
        raise StagingError("Quantity must be > 0.")

    prod = _get_product(products, product_id)
    if not prod:
        raise StagingError("Product not found.")

    try:
        qty_default = convert_to_product_default_unit(prod, qty, unit)
    except Exception as e:
        raise StagingError(f"Conversion failed: {e}")

    # Ensure layers exist (soft migrate)
    migrate_products_to_layers(products)

    on_hand = float(prod.get("quantity") or 0.0)
    if qty_default > on_hand + 1e-9:
        raise StagingError(
            f"Not enough inventory. Need {qty_default:.4f} {prod.get('default_unit')}, on hand {on_hand:.4f}."
        )

    # FIFO issue at staging time (reserve inventory), only from the chosen
    # location's stock, same as a regular Remove.
    if not location_name:
        raise StagingError("Please select a location.")
    try:
        issue_info = fifo_issue_from_location(prod, qty_default, location_name)
    except ValueError as e:
        raise StagingError(str(e))

    record = {
        "id": str(uuid.uuid4()),
        "product_id": product_id,
        "product_name": prod.get("name"),
        "default_unit": normalize_unit(prod.get("default_unit")),
        "qty_default": float(qty_default),
        "entered_qty": float(qty),
        "entered_unit": normalize_unit(unit),
        "unit_cost_snapshot": float(issue_info.get("effective_unit_cost") or 0.0),
        "weight_snapshot": prod.get("weight"),
        "value_snapshot": float(issue_info.get("issued_value") or 0.0),
        "customer": customer or None,
        "reason": reason or None,
        "notes": notes or None,
        "scheduled_date": scheduled_date or None,
        "status": "staged",
        "staged_at": now_central_iso(),
        "released_at": None,
        "voided_at": None,
        "returned_to_inventory": False,
        "fifo_pulls": issue_info.get("pulls", []),
        "fifo_issued_value": float(issue_info.get("issued_value") or 0.0),
        "packages": package_breakdown or None,
        "tanks": tanks or None,              # [{tank_id, tank_name, gal}] pulled out of tanks
        "location_id": str(location_id) if location_id else None,
        "location_name": location_name or None,
        "staged_by": (current_user() or {}).get("username"),
    }

    records = load_staging()
    records.append(record)
    save_staging(records)

    # persist product qty/layers changes
    save_products(products)
    return record


def stage_release(record_id):
    records = load_staging()
    for r in records:
        if r.get("id") == record_id:
            if (r.get("status") or "").lower() != "staged":
                raise StagingError("Only staged records can be released.")
            r["status"] = "released"
            r["released_at"] = central_time_now_str()
            r["released_by"] = (current_user() or {}).get("username")

            save_staging(records)
            append_ledger_entry("staging_picked_up", {
                "staging_id": r.get("id"),
                "product_id": r.get("product_id"),
                "product_name": r.get("product_name"),
                "qty": r.get("qty_default"),
                "location": r.get("location_name"),
                "by": r.get("released_by"),
            })
            return r
    raise StagingError("Staging record not found.")


def stage_void(record_id, return_to_inventory=False):
    records = load_staging()
    products = load_products()

    for r in records:
        if r.get("id") == record_id:
            if (r.get("status") or "").lower() != "staged":
                raise StagingError("Only staged records can be voided.")

            r["status"] = "void"
            r["voided_at"] = central_time_now_str()


            r["voided_by"] = (current_user() or {}).get("username")
            warnings = []

            if return_to_inventory:
                prod = _get_product(products, r.get("product_id"))
                if not prod:
                    raise StagingError("Original product no longer exists; cannot return to inventory.")

                # 1) bulk quantity goes back at the location it came from, at its original cost
                migrate_products_to_layers(products)
                try:
                    fifo_return(prod, r.get("fifo_pulls") or [], location=r.get("location_name"))
                except ValueError as e:
                    raise StagingError(str(e))

                # 2) packages that were sold come back as packages
                pkg_rows = r.get("packages") or []
                if pkg_rows:
                    pki_records = load_package_inventory()
                    for row in pkg_rows:
                        pqty = float(row.get("qty") or 0.0)
                        if pqty <= 0:
                            continue
                        vol_per = float(row.get("volume_per") or 0.0)
                        pki_records.append({
                            "id":            generate_next_pki_id(pki_records),
                            "product_id":    str(r.get("product_id")),
                            "package_id":    row.get("package_id"),
                            "package_name":  row.get("package_name"),
                            "quantity":      pqty,
                            "volume_per":    vol_per,
                            "unit":          row.get("unit") or "gal",
                            "total_volume":  pqty * vol_per,
                            "location_id":   r.get("location_id"),
                            "location_name": r.get("location_name"),
                            "received_at":   now_central_iso(),
                            "removed_at":    None,
                            "type":          "staged_cancel",
                            "notes":         "Staging order canceled",
                        })
                    save_package_inventory(pki_records)

                # 3) gallons that came out of tanks go back into those tanks if they still fit
                for t in (r.get("tanks") or []):
                    try:
                        apply_tank_receive(t.get("tank_id"), prod, float(t.get("gal") or 0), "gal",
                                           source="staging_cancel", notes="Staging order canceled")
                    except Exception as e:
                        warnings.append(f"{t.get('tank_name') or 'Tank'}: {e} The gallons are back in "
                                        f"inventory at {r.get('location_name') or 'the location'}, just not in the tank.")

                r["returned_to_inventory"] = True
                save_products(products)

            r["cancel_warnings"] = warnings or None
            save_staging(records)
            append_ledger_entry("staging_canceled", {
                "staging_id": r.get("id"),
                "product_id": r.get("product_id"),
                "product_name": r.get("product_name"),
                "qty": r.get("qty_default"),
                "location": r.get("location_name"),
                "returned_to_inventory": bool(return_to_inventory),
                "by": r.get("voided_by"),
            })
            return r

    raise StagingError("Staging record not found.")


def count_active_staging():
    try:
        records = load_staging()
    except Exception:
        return 0
    return sum(1 for r in records if (r.get("status") or "").lower() == "staged")


# -------------------------
# Search helper
# -------------------------
def _find_best_product_match(products, q: str):
    q = (q or "").strip().lower()
    if not q:
        return None

    exact = [p for p in products if (p.get("name") or "").strip().lower() == q]
    if len(exact) == 1:
        return exact[0]

    partials = [p for p in products if q in (p.get("name") or "").lower()]
    if len(partials) == 1:
        return partials[0]

    starts = [p for p in partials if (p.get("name") or "").lower().startswith(q)]
    if len(starts) == 1:
        return starts[0]

    return None


# -------------------------
# KPI compute
# -------------------------
def compute_inventory_value():
    products = load_products()

    total_value = 0.0
    total_products = len(products)
    total_gallons = 0.0
    total_pounds = 0.0

    for p in products:
        try:
            qty = float(p.get("quantity") or 0.0)
        except Exception:
            qty = 0.0
        try:
            unit_cost = float(p.get("unit_cost") or 0.0)
        except Exception:
            unit_cost = 0.0

        total_value += qty * unit_cost

        p_norm = dict(p)
        p_norm["default_unit"] = normalize_unit(p_norm.get("default_unit"))
        gallons, pounds = compute_display_breakdown(p_norm)

        if gallons is not None:
            total_gallons += gallons
        if pounds is not None:
            total_pounds += pounds

    return {
        "total_value": total_value,
        "total_products": total_products,
        "total_gallons": total_gallons,
        "total_pounds": total_pounds,
    }

def compute_inventory_by_location():
    """
    Roll up inventory by location using FIFO layers,
    BUT always include locations from locations.json even if totals are 0.
    """
    products = load_products()

    # Locations master list
    loc_recs = load_locations()
    # Seed map with every known location (0 totals)
    loc_map = {}
    name_to_id = {}

    for l in loc_recs:
        loc_id = str(l.get("id") or "")
        loc_name = (l.get("name") or "").strip()
        if not loc_id or not loc_name:
            continue

        name_to_id[loc_name.lower()] = loc_id
        loc_map[loc_name] = {
            "location": loc_name,
            "location_id": loc_id,
            "address": (l.get("address") or "").strip(),
            "total_value": 0.0,
            "total_gallons": 0.0,
            "total_pounds": 0.0,
            "sku_ids": set(),
        }

    # Roll up FIFO layers into the map
    for p in products:
        _ensure_layers(p)
        default_unit = normalize_unit(p.get("default_unit"))
        weight = p.get("weight")

        for layer in p.get("layers", []):
            loc = (layer.get("location") or p.get("location") or "UNASSIGNED").strip() or "UNASSIGNED"
            qty = float(layer.get("qty") or 0.0)
            cost = float(layer.get("unit_cost") or 0.0)

            # If inventory exists at a location name that isn’t in locations.json, still show it
            if loc not in loc_map:
                loc_map[loc] = {
                    "location": loc,
                    "location_id": name_to_id.get(loc.lower()),
                    "address": "",
                    "total_value": 0.0,
                    "total_gallons": 0.0,
                    "total_pounds": 0.0,
                    "sku_ids": set(),
                }

            entry = loc_map[loc]
            entry["total_value"] += qty * cost
            entry["sku_ids"].add(p.get("id"))

            tmp = {"default_unit": default_unit, "quantity": qty, "weight": weight}
            gal, lb = compute_display_breakdown(tmp)
            if gal is not None:
                entry["total_gallons"] += gal
            if lb is not None:
                entry["total_pounds"] += lb

    # Build final list
    out = []
    for loc_name, data in loc_map.items():
        out.append(
            {
                "location": data["location"],
                "location_id": data.get("location_id"),
                "address": data.get("address", ""),
                "total_value": round(float(data["total_value"]), 2),
                "total_gallons": round(float(data["total_gallons"]), 2),
                "total_pounds": round(float(data["total_pounds"]), 2),
                "sku_count": len(data["sku_ids"]),
            }
        )

    out.sort(key=lambda x: (x.get("location") or "").lower())
    return out


# -------------------------
# Routes
# -------------------------
@app.route("/")
def index():
    return redirect(url_for("home"))


@app.route("/home")
def home():
    return render_template("home.html")


@app.route("/products")
def list_products():
    products = load_products()

    derived = []
    for p in products:
        p["default_unit"] = normalize_unit(p.get("default_unit"))

        gallons, pounds = compute_display_breakdown(p)
        inv_val = compute_item_value(p)
        pkg_size = p.get("package_size_gal")
        num_packages = packages_from_gallons(gallons, pkg_size)

        derived.append(
            {
                "raw": p,
                "gallons": gallons,
                "pounds": pounds,
                "inventory_value": inv_val,
                "num_packages": num_packages,
            }
        )

    # OPTIONAL: if you pass q=... to list_products.html, you can filter there.

    # ---- KPI: total inventory value (sum of what's shown in the table) ----
    total_inventory_value = round(sum((d.get("inventory_value") or 0.0) for d in derived), 2)

    # ---- Package columns ----
    all_packages = load_packages()
    pkg_summaries = {}
    for p in products:
        pid = str(p.get("id"))
        summary = get_package_inventory_summary(pid)
        total_packaged_gal = sum(
            package_volume_to_gallons(p, t["total_volume"], t.get("unit"))
            for t in summary.values()
        )
        gal_for_prod = next(
            (d.get("gallons") or 0.0 for d in derived if str(d["raw"].get("id")) == pid), 0.0
        )
        pkg_summaries[pid] = {
            "by_package": summary,
            "unpackaged_gal": round(max(0.0, (gal_for_prod or 0.0) - total_packaged_gal), 4),
        }

    # ---- KPI: total Unpackaged gallons across all products ----
    total_unpackaged_gal = round(
        sum((v.get("unpackaged_gal") or 0.0) for v in pkg_summaries.values()), 2
    )

    return render_template(
        "list_products.html",
        app_title=APP_TITLE,
        items=derived,
        packages=all_packages,
        all_packages=all_packages,
        pkg_summaries=pkg_summaries,
        total_inventory_value=total_inventory_value,
        total_unpackaged_gal=total_unpackaged_gal,
    )


@app.get("/search")
def product_search():
    q = (request.args.get("q") or "").strip()
    if not q:
        return redirect(url_for("list_products"))

    products = load_products()
    match = _find_best_product_match(products, q)
    if match:
        return redirect(url_for("product_detail", product_id=match["id"]))

    return redirect(url_for("list_products", q=q))


@app.route("/add", methods=["GET", "POST"])
def add_product():
    locations = load_locations_for_user()  # ✅ list of dicts, e.g. [{"id":"0001","name":"Midland Yard"}, ...]

    if request.method == "POST":
        name = (request.form.get("name") or "").strip()
        weight_raw = (request.form.get("weight") or "").strip()
        default_unit = normalize_unit((request.form.get("default_unit") or "").strip().lower())
        unit_cost_raw = (request.form.get("unit_cost") or "").strip()
        if not can_see_costs():
            unit_cost_raw = unit_cost_raw or "0"   # field is hidden; real cost comes in with Receive
        phase = (request.form.get("phase") or "").strip().lower()

        cas = (request.form.get("cas") or "").strip() or None
        supplier = (request.form.get("supplier") or "").strip() or None
        package_type = (request.form.get("package_type") or "").strip() or None
        package_size_gal_raw = (request.form.get("package_size_gal") or "").strip()

        # ✅ swap from free-text "location" to dropdown "location_id"
        location_id = (request.form.get("location_id") or "").strip() or None

        notes = (request.form.get("notes") or "").strip() or None

        errors = []

        if not name:
            errors.append("Name is required.")
        if phase not in PHASES:
            errors.append("Phase must be 'liquid' or 'solid'.")

        # Location is optional here; stock gets its location on Receive.

        try:
            unit_cost = float(unit_cost_raw)
            if unit_cost < 0:
                errors.append("Unit cost must be ≥ 0.")
        except ValueError:
            errors.append("Unit cost must be a number.")

        # New products start empty. Stock comes in through Receive on Adjust Inventory,
        # so every gallon has a real FIFO cost, location, and (optionally) packages.
        quantity = 0.0

        # unit rules
        if phase == "liquid":
            if default_unit not in UNITS_LIQUID:
                errors.append("For liquids, default unit must be gal, lb, or unit.")
        else:
            if default_unit not in UNITS_SOLID:
                errors.append("For solids, default unit must be lb or unit.")

        # weight rules
        weight = None
        if phase == "liquid":
            if default_unit in ("gal", "lb"):
                if weight_raw == "":
                    errors.append("For liquids, Weight (lb/gal) must be numeric and > 0 when unit is gal or lb.")
                else:
                    try:
                        weight = float(weight_raw)
                        if weight <= 0:
                            errors.append("For liquids, Weight (lb/gal) must be > 0 when unit is gal or lb.")
                    except ValueError:
                        errors.append("For liquids, Weight (lb/gal) must be numeric.")
            else:
                if weight_raw != "":
                    try:
                        weight = float(weight_raw)
                        if weight <= 0:
                            errors.append("If provided, Weight (lb/gal) must be > 0.")
                    except ValueError:
                        errors.append("If provided, Weight (lb/gal) must be numeric.")
        else:
            weight = None

        # package size optional
        package_size_gal = None
        if package_size_gal_raw != "":
            try:
                package_size_gal = float(package_size_gal_raw)
                if package_size_gal <= 0:
                    errors.append("Package size (gal) must be > 0 when provided.")
            except ValueError:
                errors.append("Package size (gal) must be a number when provided.")

        if errors:
            return render_template(
                "add_product.html",
                app_title=APP_TITLE,
                errors=errors,
                form=request.form,
                locations=locations,  # ✅
            )

        products = load_products()
        new_id = generate_next_product_id(products)

        # ✅ optional: map location_id -> location name for display/storage
        location_name = None
        if location_id:
            loc = next((l for l in locations if str(l.get("id")) == str(location_id)), None)
            location_name = (loc or {}).get("name")

        product = {
            "id": new_id,
            "name": name,
            "phase": phase,
            "cas": cas,
            "weight": weight,
            "default_unit": unit_to_display(default_unit),
            "unit_cost": unit_cost,
            "quantity": quantity,
            "supplier": supplier,
            "package_type": package_type,
            "package_size_gal": package_size_gal,

            # ✅ recommended: store BOTH for now (safe migration)
            "location_id": location_id,
            "location": location_name,  # keeps old templates working

            "notes": notes,
            "last_updated": now_central_iso(),
            "layers": [],
        }

        products.append(product)
        save_products(products)
        append_ledger_entry("product_created", {"product_id": new_id, "name": name,
                                                "by": (current_user() or {}).get("username")})
        flash(f"{name} was added. Use Receive on Adjust Inventory to bring stock in.", "success")
        return redirect(url_for("list_products"))

    return render_template(
        "add_product.html",
        app_title=APP_TITLE,
        errors=None,
        form={},
        locations=locations,  # ✅
    )
@app.route("/inventory/receive", methods=["GET", "POST"])
def inventory_receive_page():
    products = load_products()
    locations = load_locations_for_user()
    tanks = load_tanks()

    # location_id -> list of tanks
    tanks_by_loc = {}
    for t in tanks:
        if not t.get("is_active", True):
            continue
        lid = str(t.get("location_id"))
        tanks_by_loc.setdefault(lid, []).append({
            "id": str(t.get("id")),
            "name": t.get("name") or str(t.get("id")),
            "capacity_gal": _safe_float(t.get("capacity_gal"), 0.0),
        })

    # sort tanks per location
    for lid in tanks_by_loc:
        tanks_by_loc[lid].sort(key=lambda x: x["name"].lower())

    if request.method == "POST":
        product_id = (request.form.get("product_id") or "").strip()
        qty_raw = (request.form.get("qty") or "").strip()
        unit_in = normalize_unit((request.form.get("unit") or "").strip().lower())
        location_id = (request.form.get("location_id") or "").strip()
        tank_id = (request.form.get("tank_id") or "").strip() or None
        ref = (request.form.get("ref") or "").strip() or None
        notes = (request.form.get("notes") or "").strip() or None
        receive_cost_raw = (request.form.get("receive_unit_cost") or "").strip()

        errors = []

        prod = next((p for p in products if str(p.get("id")) == str(product_id)), None)
        if not prod:
            errors.append("Please select a product.")

        loc = get_location_by_id(locations, location_id) if location_id else None
        if not loc:
            errors.append("Please select a location.")

        try:
            qty = float(qty_raw)
            if qty <= 0:
                errors.append("Quantity must be > 0.")
        except ValueError:
            errors.append("Quantity must be a number.")

        # We only allow GAL/LB for tank receive (since tanks are liquids)
        if unit_in not in ("gal", "lb"):
            errors.append("Unit must be GAL or LB for tank receipts.")

        # Receive cost (keep consistent with FIFO receive)
        try:
            recv_cost = float(receive_cost_raw)
            if recv_cost < 0:
                errors.append("Cost must be ≥ 0.")
        except ValueError:
            errors.append("Cost must be a number.")

        # Validate tank belongs to selected location
        if tank_id:
            t = get_tank_by_id(load_tanks(), tank_id)
            if not t:
                errors.append("Selected tank was not found.")
            elif str(t.get("location_id")) != str(location_id):
                errors.append("Selected tank does not belong to the selected location.")

        # If product is solid, tanks don't apply
        if prod and (prod.get("phase") or "").lower() == "solid":
            errors.append("Solid products cannot be received into tanks.")

        if errors:
            return render_template(
                "receive_inventory.html",
                app_title=APP_TITLE,
                errors=errors,
                form=request.form,
                products=products,
                locations=locations,
                tanks_by_loc=tanks_by_loc,
            )

        # ---- Apply to product inventory using your existing FIFO layer system ----
        migrate_products_to_layers(products)

        # Convert entered qty/unit (gal/lb) into product default unit qty for FIFO
        try:
            qty_default = convert_to_product_default_unit(prod, qty, unit_in)
        except Exception as e:
            return render_template(
                "receive_inventory.html",
                app_title=APP_TITLE,
                errors=[str(e)],
                form=request.form,
                products=products,
                locations=locations,
                tanks_by_loc=tanks_by_loc,
            )

        # Use location name for FIFO layer location (keeps your current location rollups working)
        effective_location = (loc.get("name") or "").strip() or None
        fifo_receive(prod, qty_default, recv_cost, location=effective_location)

        # ---- Optional tank ledger write (in gallons) ----
        if tank_id:
            try:
                apply_tank_receive(
                    tank_id=tank_id,
                    product=prod,
                    qty_in=qty,
                    unit_in=unit_in,
                    source="receive",
                    ref=ref,
                    notes=notes,
                )
            except ValueError as e:
                # rollback the FIFO receive (best-effort) by issuing back what we just received
                try:
                    fifo_issue(prod, qty_default)
                except Exception:
                    pass

                return render_template(
                    "receive_inventory.html",
                    app_title=APP_TITLE,
                    errors=[str(e)],
                    form=request.form,
                    products=products,
                    locations=locations,
                    tanks_by_loc=tanks_by_loc,
                )

        prod["last_updated"] = now_central_iso()
        save_products(products)

        flash("Inventory received successfully.", "success")
        return redirect(url_for("inventory_receive_page"))

    return render_template(
        "receive_inventory.html",
        app_title=APP_TITLE,
        errors=None,
        form={},
        products=products,
        locations=locations,
        tanks_by_loc=tanks_by_loc,
    )


@app.route("/locations/<location_id>/tanks")
def tanks_page(location_id):
    locations = load_locations_safe()
    loc = get_location_by_id(locations, location_id)
    if not loc:
        flash("Location not found.", "danger")
        return redirect(url_for("locations_page"))

    tanks = get_tanks_for_location(load_tanks(), location_id)
    ledger = load_tank_ledger()
    products = load_products()

    # Build view models with computed fill + status
    tank_cards = []
    for t in tanks:
        tid = t.get("id")
        cap = _safe_float(t.get("capacity_gal"), 0.0)
        fill = get_tank_fill_gal(ledger, tid)
        pct, label = tank_status(fill, cap)

        assigned_pid = t.get("assigned_product_id") or None
        assigned_name = product_name_by_id(products, assigned_pid) if assigned_pid else None

        tank_cards.append({
            "id": tid,
            "name": t.get("name") or tid,
            "capacity_gal": cap,
            "fill_gal": fill,
            "pct_full": pct,
            "status": label,  # empty/near_empty/ok/near_full/full
            "assigned_product_id": assigned_pid,
            "assigned_product_name": assigned_name,
        })

    # Optional: sort by tank name
    tank_cards.sort(key=lambda x: str(x["name"]).lower())

    return render_template(
        "tanks_list.html",
        app_title=APP_TITLE,
        location=loc,
        tanks=tank_cards,
    )

@app.route("/locations/<location_id>/tanks/add", methods=["GET", "POST"])
def add_tank(location_id):
    locations = load_locations_for_user()
    loc = get_location_by_id(locations, location_id)
    if not loc:
        flash("Location not found.", "danger")
        return redirect(url_for("locations_page"))

    if request.method == "POST":
        name = (request.form.get("name") or "").strip()
        cap_raw = (request.form.get("capacity_gal") or "").strip()
        notes = (request.form.get("notes") or "").strip() or None

        errors = []
        if not name:
            errors.append("Tank name is required.")

        try:
            capacity_gal = float(cap_raw)
            if capacity_gal <= 0:
                errors.append("Capacity must be > 0 gallons.")
        except ValueError:
            errors.append("Capacity must be a number (gallons).")

        if errors:
            return render_template(
                "add_tank.html",
                app_title=APP_TITLE,
                location=loc,
                errors=errors,
                form=request.form,
            )

        tanks = load_tanks()
        new_id = generate_next_tank_id(tanks)

        tank = {
            "id": new_id,
            "location_id": str(location_id),
            "name": name,
            "capacity_gal": float(capacity_gal),   # always gallons
            "assigned_product_id": None,           # locks when first filled
            "is_active": True,
            "notes": notes,
            "created_at": now_central_iso(),
        }

        tanks.append(tank)
        save_tanks(tanks)

        return redirect(url_for("tanks_page", location_id=location_id))

    return render_template(
        "add_tank.html",
        app_title=APP_TITLE,
        location=loc,
        errors=None,
        form={},
    )

@app.route("/product/<product_id>", methods=["GET", "POST"])
def product_detail(product_id):
    products = load_products()
    idx, prod = get_product_by_id(products, product_id)
    if prod is None:
        return redirect(url_for("list_products"))
    # make sure layers exists so the template can safely render it
    _ensure_layers(prod)
    location_rows = compute_product_location_breakdown(prod)


    if request.method == "POST":
        name = (request.form.get("name") or "").strip()
        default_unit = normalize_unit((request.form.get("default_unit") or "").strip().lower())
        unit_cost_raw = (request.form.get("unit_cost") or "").strip()
        if not can_see_costs():
            unit_cost_raw = str(prod.get("unit_cost") or 0)   # hidden field: keep the current cost
        quantity_raw = (request.form.get("quantity") or "").strip()
        weight_raw = (request.form.get("weight") or "").strip()
        phase = (request.form.get("phase") or "").strip().lower()

        cas = (request.form.get("cas") or "").strip() or None
        supplier = (request.form.get("supplier") or "").strip() or None
        package_type = (request.form.get("package_type") or "").strip() or None
        package_size_gal_raw = (request.form.get("package_size_gal") or "").strip()
        location = (request.form.get("location") or "").strip() or None
        notes = (request.form.get("notes") or "").strip() or None

        errors = []
        weight = None
        package_size_gal = None

        if not name:
            errors.append("Name is required.")
        if phase not in PHASES:
            errors.append("Phase must be 'liquid' or 'solid'.")

        try:
            unit_cost = float(unit_cost_raw)
            if unit_cost < 0:
                errors.append("Unit cost must be ≥ 0.")
        except ValueError:
            errors.append("Unit cost must be a number.")

        # New products start empty. Stock comes in through Receive on Adjust Inventory,
        # so every gallon has a real FIFO cost, location, and (optionally) packages.
        quantity = 0.0

        if phase == "liquid":
            if default_unit not in UNITS_LIQUID:
                errors.append("For liquids, default unit must be gal, lb, or unit.")
        else:
            if default_unit not in UNITS_SOLID:
                errors.append("For solids, default unit must be lb or unit.")

        if phase == "liquid":
            if default_unit in ("gal", "lb"):
                if weight_raw == "":
                    errors.append("For liquids, Weight (lb/gal) must be numeric and > 0 when unit is gal or lb.")
                else:
                    try:
                        weight = float(weight_raw)
                        if weight <= 0:
                            errors.append("For liquids, Weight (lb/gal) must be > 0 when unit is gal or lb.")
                    except ValueError:
                        errors.append("For liquids, Weight (lb/gal) must be numeric.")
            else:
                if weight_raw != "":
                    try:
                        weight = float(weight_raw)
                        if weight <= 0:
                            errors.append("If provided, Weight (lb/gal) must be > 0.")
                    except ValueError:
                        errors.append("If provided, Weight (lb/gal) must be numeric.")
        else:
            weight = None

        if package_size_gal_raw != "":
            try:
                package_size_gal = float(package_size_gal_raw)
                if package_size_gal <= 0:
                    errors.append("Package size (gal) must be > 0 when provided.")
            except ValueError:
                errors.append("Package size (gal) must be a number when provided.")

        if errors:
            return render_template(
                "edit_product.html",
                app_title=APP_TITLE,
                errors=errors,
                p=prod,
                form=request.form,
                location_rows=location_rows,
            )


        # Only the product's details change here. Stock (FIFO layers) is left
        # exactly as it is; it only moves through Receive/Remove/Move/Blend.
        prod.update(
            {
                "name": name,
                "cas": cas,
                "phase": phase,
                "default_unit": unit_to_display(default_unit),  # 🔥 store ALL CAPS
                "weight": weight,
                "supplier": supplier,
                "package_type": package_type,
                "package_size_gal": package_size_gal,
                "location": location,
                "notes": notes,
                "last_updated": now_central_iso(),
            }
        )


        _sync_product_qty_and_avg_cost_from_layers(prod)

        products[idx] = prod
        save_products(products)
        return redirect(url_for("list_products"))

    prod["default_unit"] = normalize_unit(prod.get("default_unit"))
    return render_template(
        "edit_product.html",
        app_title=APP_TITLE,
        errors=None,
        p=prod,
        form=prod,
        location_rows=location_rows,
    )


@app.route("/delete/<product_id>", methods=["POST"])
def delete_product(product_id):
    products = load_products()
    idx, _ = get_product_by_id(products, product_id)
    if idx is not None:
        del products[idx]
        save_products(products)
    return redirect(url_for("list_products"))

def _product_unit_cost(prod) -> float:
    """Average FIFO cost per the product's own unit, falling back to its listed unit cost."""
    try:
        qty = float(prod.get("quantity") or 0)
        if qty > 0:
            value = float(compute_item_value(prod) or 0)
            if value > 0:
                return value / qty
    except Exception:
        pass
    try:
        return float(prod.get("unit_cost") or 0)
    except Exception:
        return 0.0


def formula_cost_per_unit(formula, by_id):
    """
    Cost to make 1 unit (GAL or LB, the formula's default unit) of a percent formula,
    using each component's current FIFO cost. Returns (cost, unit) or (None, unit)
    if a component is missing or can't be converted (e.g. no weight set).
    """
    unit = normalize_unit(((formula.get("defaults") or {}).get("target_unit") or "gal").lower())
    if unit not in ("gal", "lb"):
        unit = "gal"
    comps = formula.get("components") or []
    if not comps or (formula.get("mode") or "percent") != "percent":
        return None, unit
    total = 0.0
    for c in comps:
        prod = by_id.get(str(c.get("product_id") or ""))
        if not prod:
            return None, unit
        try:
            pct = float(c.get("percent") or 0)
            q_prod, _unit_str, _vol = convert_required_to_product_unit(prod, pct / 100.0, unit)
            total += float(q_prod) * _product_unit_cost(prod)
        except Exception:
            return None, unit
    return round(total, 2), unit


@app.get("/formulas")
def formulas_page():
    formulas = load_formulas()
    formulas.sort(key=lambda x: (x.get("name") or "").lower())
    by_id = index_products_by_id(load_products())
    rows = []
    for f in formulas:
        cost, unit = formula_cost_per_unit(f, by_id)
        rows.append({
            "formula": f,
            "component_count": len(f.get("components") or []),
            "cost": cost,
            "unit": unit,
        })
    return render_template("formulas.html", app_title=APP_TITLE, rows=rows)

@app.post("/formulas/create")
def formulas_create():
    name = (request.form.get("name") or "").strip()
    description = (request.form.get("description") or "").strip()

    if not name:
        flash("Formula name is required.", "danger")
        return redirect(url_for("formulas_page"))

    formulas = load_formulas()
    now = now_central_iso()

    formulas.append({
        "id": str(uuid.uuid4()),
        "name": name,
        "description": description or None,
        "mode": "percent",          # default for now
        "defaults": {
            "target_qty": None,
            "target_unit": "gal"
        },
        "components": [],           # will be filled by “Save from Blend”
        "tags": [],
        "created_at": now,
        "updated_at": now,
    })

    save_formulas(formulas)
    flash("Formula created.", "success")
    return redirect(url_for("formulas_page"))


@app.post("/formulas/<formula_id>/delete")
def formulas_delete(formula_id):
    formulas = load_formulas()
    new_list = [f for f in formulas if str(f.get("id")) != str(formula_id)]
    if len(new_list) == len(formulas):
        flash("Formula not found.", "danger")
    else:
        save_formulas(new_list)
        flash("Formula deleted.", "success")
    return redirect(url_for("formulas_page"))


# -------------------------
# Inventory Adjust (add/remove + optional staging) using FIFO
# -------------------------
@app.route("/inventory/adjust", methods=["GET", "POST"])
def inventory_adjust_page():
    products = load_products()
    locations = load_locations_for_user()
    tanks = load_tanks()

    # -------------------------
    # Tanks map for Move tab
    # -------------------------
    # Every tank per location with its current contents (used by Receive, Remove,
    # Move and Repackage to show only the tanks that make sense for the product)
    products_by_id = {str(p.get("id")): p for p in products}
    tanks_by_loc = {}
    for lid in {str(t.get("location_id") or "") for t in tanks if t.get("is_active", True)}:
        if lid:
            tanks_by_loc[lid] = tank_rows_for_location(lid, products_by_id)

    def tank_at(location_id, tid):
        return next((t for t in tanks_by_loc.get(str(location_id or ""), []) if t["id"] == tid), None)

    def tank_choice(field, location_id):
        """(tank_row, error) for the tank picked in `field`, or (None, None) if no tank was picked."""
        tid = (request.form.get(field) or "").strip()
        if not tid:
            return None, None
        row = next((t for t in tanks_by_loc.get(str(location_id or ""), []) if t["id"] == tid), None)
        if not row:
            return None, "That tank isn't at the selected location."
        return row, None

    def loc_name_from_id(lid: str | None):
        if not lid:
            return None
        rec = next((l for l in locations if str(l.get("id")) == str(lid)), None)
        return (rec or {}).get("name")

    # -------------------------
    # Local helper: remove FIFO from a specific location
    # (keeps your FIFO layers structure, syncs qty/avg cost from layers)
    # -------------------------

    if request.method == "POST":
        next_url = (request.form.get("next") or "").strip()
        action = (request.form.get("action") or "add").strip().lower()  # add | remove | move | repackage

        product_id = (request.form.get("product_id") or "").strip()
        qty_raw = (request.form.get("qty") or "").strip()
        unit = normalize_unit((request.form.get("unit") or "").strip().lower())
        notes = (request.form.get("notes") or "").strip() or None
        remove_mode = (request.form.get("remove_mode") or "bulk").strip().lower()  # bulk | package

        errors = []

        prod = next((p for p in products if str(p.get("id")) == str(product_id)), None)
        if not prod:
            errors.append("Please select a product.")

        # "Sell/Remove by package type" — user picks package rows instead of a raw qty/unit
        selling_by_package = (action == "remove" and remove_mode == "package")

        qty = None
        if not selling_by_package:
            try:
                qty = float(qty_raw)
                if qty <= 0:
                    errors.append("Quantity must be > 0.")
            except ValueError:
                errors.append("Quantity must be a number.")

        # -------------------------
        # MOVE FLOW
        # -------------------------
        if action == "move":
            # Move supports GAL/LB (tank compatible)
            if unit not in ("gal", "lb"):
                errors.append("Move supports GAL or LB only (tank-compatible).")

            from_location_id = (request.form.get("from_location_id") or "").strip() or None
            to_location_id = (request.form.get("to_location_id") or "").strip() or None
            from_tank_id = (request.form.get("from_tank_id") or "").strip() or None
            to_tank_id = (request.form.get("to_tank_id") or "").strip() or None

            if not from_location_id or not to_location_id:
                errors.append("From and To locations are required.")

            from_loc_name = loc_name_from_id(from_location_id)
            to_loc_name = loc_name_from_id(to_location_id)
            if from_location_id and not from_loc_name:
                errors.append("From location not found.")
            if to_location_id and not to_loc_name:
                errors.append("To location not found.")

            # solids can't go into tanks
            if prod and (prod.get("phase") or "").lower() == "solid":
                if from_tank_id or to_tank_id:
                    errors.append("Solid products cannot be moved into/out of tanks.")

            # Validate tanks belong to their location (NO writes yet)
            if from_tank_id:
                t = get_tank_by_id(tanks, from_tank_id)
                if not t:
                    errors.append("FROM tank not found.")
                elif str(t.get("location_id")) != str(from_location_id):
                    errors.append("FROM tank does not belong to FROM location.")

            if to_tank_id:
                t = get_tank_by_id(tanks, to_tank_id)
                if not t:
                    errors.append("TO tank not found.")
                elif str(t.get("location_id")) != str(to_location_id):
                    errors.append("TO tank does not belong to TO location.")

            if errors:
                return render_template(
                    "inventory_adjust.html",
                    app_title=APP_TITLE,
                    errors=errors,
                    products=products,
                    staged=load_staging(),
                    form=request.form,
                    locations=locations,
                    tanks_by_loc=tanks_by_loc,
                )

            # Ensure FIFO layers exist
            migrate_products_to_layers(products)
            _ensure_layers(prod)

            # convert entered qty into product default unit for FIFO movement
            try:
                qty_default = convert_to_product_default_unit(prod, qty, unit)
            except Exception as e:
                return render_template(
                    "inventory_adjust.html",
                    app_title=APP_TITLE,
                    errors=[str(e)],
                    products=products,
                    staged=load_staging(),
                    form=request.form,
                    locations=locations,
                    tanks_by_loc=tanks_by_loc,
                )

            # ---- 1) Move FIFO layers from from_loc_name -> to_loc_name ----
            remaining = float(qty_default)
            pulls = []
            new_layers = []

            for layer in (prod.get("layers") or []):
                loc = (layer.get("location") or "UNASSIGNED").strip()
                lqty = float(layer.get("qty") or 0.0)
                lcost = float(layer.get("unit_cost") or 0.0)

                if remaining > 1e-12 and loc.lower() == from_loc_name.lower() and lqty > 0:
                    take = min(lqty, remaining)
                    pulls.append({"qty": take, "unit_cost": lcost})
                    lqty -= take
                    remaining -= take

                if lqty > 1e-9:
                    layer["qty"] = round(lqty, 4)
                    new_layers.append(layer)

            if remaining > 1e-9:
                return render_template(
                    "inventory_adjust.html",
                    app_title=APP_TITLE,
                    errors=[f"Not enough inventory at {from_loc_name} to move {qty_default:.4f} {prod.get('default_unit')}."],
                    products=products,
                    staged=load_staging(),
                    locations=locations,
                    tanks_by_loc=tanks_by_loc,
                    form=request.form,
                )

            # Add moved qty into destination layers (preserve costs)
            for p_pull in pulls:
                new_layers.append({
                    "qty": round(float(p_pull["qty"]), 4),
                    "unit": normalize_unit(prod.get("default_unit")),
                    "unit_cost": round(float(p_pull["unit_cost"]), 4),
                    "datetime": central_time_now_str(),
                    "location": to_loc_name,
                })

            prod["layers"] = new_layers
            _sync_product_qty_and_avg_cost_from_layers(prod)

            # ---- 2) Tank ledger deltas (optional) ----
            # Only do tank writes AFTER FIFO succeeded.
            if from_tank_id:
                apply_tank_issue(
                    tank_id=from_tank_id,
                    product=prod,
                    qty_out=qty,
                    unit_out=unit,
                    source="move_out",
                    ref=None,
                    notes=notes,
                )

            if to_tank_id:
                apply_tank_receive(
                    tank_id=to_tank_id,
                    product=prod,
                    qty_in=qty,
                    unit_in=unit,
                    source="move_in",
                    ref=None,
                    notes=notes,
                )

            if from_tank_id:
                maybe_unlock_tank_if_empty(from_tank_id)

            prod["last_updated"] = central_time_now_str()
            save_products(products)
            flash("Inventory moved successfully.", "success")
            return redirect(next_url or url_for("inventory_adjust_page"))

        # -------------------------
        # REPACKAGE FLOW
        # Moves product between containers at ONE location. Sources:
        #   loose   - Unpackaged stock that isn't sitting in a tank
        #   tank    - gallons coming out of a tank at this location
        #   package - packages already on hand being opened (tote -> pails,
        #             drum -> tank, case -> bottles, ...)
        # Destinations: any mix of package types and/or tanks.
        #
        # Packaging is a view of the bulk FIFO total, not a deduction from it,
        # so repackaging never touches FIFO or cost -- EXCEPT the optional
        # "loss" amount (spillage, residue left in the container), which is
        # issued out of FIFO at cost so it doesn't linger as phantom stock.
        # When a package is opened and not all of it is refilled, whatever is
        # left over falls back into Unpackaged automatically, because
        # Unpackaged = bulk on hand - packaged on hand.
        # -------------------------
        if action == "repackage":
            def _repack_error(msgs):
                return render_template(
                    "inventory_adjust.html",
                    app_title=APP_TITLE,
                    errors=msgs if isinstance(msgs, list) else [msgs],
                    products=products,
                    staged=load_staging(),
                    locations=locations,
                    tanks_by_loc=tanks_by_loc,
                    packages=load_packages(),
                    form=request.form,
                )

            # Older forms had no source field: a picked tank meant "from tank".
            source_type = (request.form.get("repack_source") or "").strip().lower()
            if not source_type:
                source_type = "tank" if (request.form.get("tank_id") or "").strip() else "loose"
            if source_type not in ("loose", "tank", "package"):
                errors.append("Pick where the product is coming from.")

            if unit not in ("gal", "lb"):
                errors.append("Repackage supports GAL or LB only.")

            repack_location_id = (request.form.get("location_id") or "").strip() or None
            repack_loc_name = loc_name_from_id(repack_location_id) if repack_location_id else None
            if not repack_location_id:
                errors.append("Please select a location.")
            elif not repack_loc_name:
                errors.append("Location not found.")

            # ---- Optional loss (spillage / residue) ----
            loss_raw = (request.form.get("loss_qty") or "").strip()
            loss_unit = normalize_unit((request.form.get("loss_unit") or "gal").strip().lower())
            loss_qty = 0.0
            if loss_raw:
                try:
                    loss_qty = float(loss_raw)
                    if loss_qty < 0:
                        errors.append("Loss can't be negative.")
                except (ValueError, TypeError):
                    errors.append("Loss must be a number.")
            if loss_qty > 0 and loss_unit not in ("gal", "lb"):
                errors.append("Loss must be in GAL or LB.")

            if errors:
                return _repack_error(errors)

            all_packages = load_packages()
            pkg_by_id = {str(pk.get("id")): pk for pk in all_packages}

            # ---- Source: packages being opened ----
            src_pkg_def = None
            src_pkg_id = None
            src_pkg_qty = 0.0
            src_vol_per = 0.0
            src_pkg_unit = "gal"
            if source_type == "package":
                src_pkg_id = (request.form.get("source_package_id") or "").strip()
                src_pkg_def = pkg_by_id.get(src_pkg_id)
                if not src_pkg_def:
                    errors.append("Pick the package type you're opening.")
                try:
                    src_pkg_qty = float((request.form.get("source_package_qty") or "").strip())
                    if src_pkg_qty <= 0 or not float(src_pkg_qty).is_integer():
                        errors.append("Number of packages to open must be a whole number greater than 0.")
                except (ValueError, TypeError):
                    errors.append("Number of packages to open must be a number.")
                if src_pkg_def and not errors:
                    src_vol_per = float(src_pkg_def.get("volume") or 0.0)
                    src_pkg_unit = normalize_unit(src_pkg_def.get("unit") or "gal")
                    on_hand_pkgs = (get_package_inventory_summary_for_location(product_id, repack_location_id)
                                    .get(src_pkg_id, {}).get("quantity", 0.0))
                    if src_pkg_qty > on_hand_pkgs + 1e-9:
                        errors.append(
                            f"Only {on_hand_pkgs:g} x {src_pkg_def.get('name')} of {prod.get('name')} "
                            f"on hand at {repack_loc_name}."
                        )

            # ---- Destination rows: packages and/or tanks being filled ----
            pkg_ids  = request.form.getlist("repackage_package_id[]")
            pkg_qtys = request.form.getlist("repackage_package_qty[]")

            requested_by_pkg = {}
            for pid_raw, qraw in zip(pkg_ids, pkg_qtys):
                pid = (pid_raw or "").strip()
                qraw = (qraw or "").strip()
                if not pid or not qraw:
                    continue
                try:
                    pqty = float(qraw)
                except (ValueError, TypeError):
                    errors.append("Package quantity must be a number.")
                    continue
                if pqty <= 0:
                    continue
                requested_by_pkg[pid] = requested_by_pkg.get(pid, 0.0) + pqty

            if not requested_by_pkg and not errors:
                errors.append("Add at least one package type or tank to fill.")

            source_tank_id = (request.form.get("tank_id") or "").strip() if source_type == "tank" else ""

            package_rows_parsed = []
            packaged_default_total = 0.0   # everything going INTO packages + tanks, default unit
            dest_tanks = []                # [(tank_row, gallons)]
            if prod and not errors:
                for pid, pqty in requested_by_pkg.items():
                    if pid.startswith("tank:"):
                        trow = tank_at(repack_location_id, pid[5:])
                        if (prod.get("phase") or "").lower() == "solid":
                            errors.append("Solid products can't go into tanks.")
                            continue
                        problem = tank_receive_problem(trow, product_id, pqty) if trow else "That tank isn't at the selected location."
                        if problem:
                            errors.append(problem)
                            continue
                        if source_tank_id and source_tank_id == trow["id"]:
                            errors.append(f"You're filling from {trow['name']}, so it can't also be where it's going.")
                            continue
                        try:
                            packaged_default_total += convert_to_product_default_unit(prod, pqty, "gal")
                        except Exception as e:
                            errors.append(str(e))
                            continue
                        dest_tanks.append((trow, round(pqty, 4)))
                        continue

                    pkg_def = pkg_by_id.get(pid)
                    if not pkg_def:
                        errors.append("Unknown package type selected.")
                        continue
                    if source_type == "package" and pid == src_pkg_id:
                        errors.append(f"You're opening {pkg_def.get('name')}, so it can't also be what you're filling.")
                        continue
                    if not float(pqty).is_integer():
                        errors.append(f"{pkg_def.get('name')}: number of containers must be a whole number.")
                        continue

                    vol_per = float(pkg_def.get("volume") or 0.0)
                    pkg_unit = normalize_unit(pkg_def.get("unit") or "gal")
                    try:
                        row_default = convert_to_product_default_unit(prod, pqty * vol_per, pkg_unit)
                    except Exception as e:
                        errors.append(f"{pkg_def.get('name')}: {e}")
                        continue

                    packaged_default_total += row_default
                    package_rows_parsed.append({
                        "package_id":   pid,
                        "package_name": pkg_def.get("name"),
                        "qty":          pqty,
                        "volume_per":   vol_per,
                        "unit":         pkg_unit,
                    })

            if errors:
                return _repack_error(errors)

            packaged_default_total = round(packaged_default_total, 4)
            default_unit = prod.get("default_unit") or ""

            try:
                loss_default = round(convert_to_product_default_unit(prod, loss_qty, loss_unit), 4) if loss_qty > 0 else 0.0
            except Exception as e:
                return _repack_error(f"Loss: {e}")

            # Ensure FIFO layers exist and work out what's at this location
            migrate_products_to_layers(products)
            _ensure_layers(prod)

            chosen_loc = (repack_loc_name or "UNASSIGNED").strip()
            loc_on_hand = 0.0
            for layer in (prod.get("layers") or []):
                if (layer.get("location") or "UNASSIGNED").strip().lower() == chosen_loc.lower():
                    loc_on_hand += float(layer.get("qty") or 0.0)

            already_packaged_default = get_packaged_default_qty_for_location(prod, repack_location_id)
            unpackaged_on_hand = max(0.0, loc_on_hand - already_packaged_default)

            repack_tank = None
            repack_gal = None
            src_default = 0.0       # how much the source gives up, default unit
            leftover_default = 0.0  # package source only: what falls back to Unpackaged

            if source_type == "package":
                try:
                    src_default = round(convert_to_product_default_unit(prod, src_pkg_qty * src_vol_per, src_pkg_unit), 4)
                except Exception as e:
                    return _repack_error(f"{src_pkg_def.get('name')}: {e}")

                used_default = packaged_default_total + loss_default
                tolerance = max(0.01, src_default * 0.001)
                if used_default > src_default + tolerance:
                    return _repack_error(
                        f"Opening {src_pkg_qty:g} x {src_pkg_def.get('name')} gives {src_default:.4f} {default_unit}, "
                        f"but you're filling {packaged_default_total:.4f}"
                        + (f" plus {loss_default:.4f} loss" if loss_default else "")
                        + f" {default_unit}. Open more packages or fill fewer."
                    )
                leftover_default = round(max(0.0, src_default - used_default), 4)
                if loss_default > loc_on_hand + 1e-9:
                    return _repack_error(f"Loss is more than the {loc_on_hand:.4f} {default_unit} on hand at {chosen_loc}.")

            else:
                # Loose or tank: the hidden qty is the destination total worked out
                # by the page; it should agree with the rows (catches tampering/typos).
                try:
                    dest_from_qty = convert_to_product_default_unit(prod, qty, unit)
                except Exception as e:
                    return _repack_error(str(e))
                tolerance = max(0.05, dest_from_qty * 0.01)
                if abs(packaged_default_total - dest_from_qty) > tolerance:
                    return _repack_error(
                        f"Packaged volume ({packaged_default_total:.4f} {default_unit}) doesn't match "
                        f"the quantity submitted ({dest_from_qty:.4f} {default_unit}). Re-check the package rows."
                    )

                src_default = round(packaged_default_total + loss_default, 4)
                try:
                    repack_gal = round(_default_qty_to_gal(prod, src_default), 4)
                except Exception as e:
                    return _repack_error(str(e))

                if source_type == "tank":
                    repack_tank, tank_err = tank_choice("tank_id", repack_location_id)
                    if not tank_err and not repack_tank:
                        tank_err = "Pick the tank you're filling from."
                    if not tank_err:
                        tank_err = tank_issue_problem(repack_tank, product_id, repack_gal)
                    if tank_err:
                        return _repack_error(tank_err)
                else:
                    in_tanks_gal = product_tank_gal(product_id, repack_location_id)
                    try:
                        loose_gal = max(0.0, _default_qty_to_gal(prod, unpackaged_on_hand) - in_tanks_gal)
                    except Exception:
                        loose_gal = None
                    if loose_gal is not None and in_tanks_gal > 0 and repack_gal > loose_gal + 1e-6:
                        return _repack_error(
                            f"Only {loose_gal:g} gal of {prod.get('name')} is loose at {chosen_loc}; "
                            f"{in_tanks_gal:g} gal is in tanks. Pick \"A tank\" under Coming from."
                        )

                if src_default > unpackaged_on_hand + 1e-9:
                    return _repack_error(
                        f"Cannot repackage {src_default:.4f} {default_unit} from {chosen_loc} — "
                        f"only {unpackaged_on_hand:.4f} Unpackaged on hand at that location "
                        f"({loc_on_hand:.4f} total, {already_packaged_default:.4f} already packaged)."
                    )

            # ================= All checks passed: write =================
            repack_group = "RPK-" + uuid.uuid4().hex[:10].upper()
            stamp_time = now_central_iso()

            # 1) Loss leaves the books at FIFO cost (the only FIFO change here)
            loss_info = None
            if loss_default > 0:
                try:
                    loss_info = fifo_issue_from_location(prod, loss_default, chosen_loc)
                except ValueError as e:
                    return _repack_error(str(e))

            # 2) Package records: opened packages out, new packages in
            pki_records = load_package_inventory()
            if source_type == "package":
                pki_records.append({
                    "id":            generate_next_pki_id(pki_records),
                    "product_id":    str(product_id),
                    "package_id":    src_pkg_id,
                    "package_name":  src_pkg_def.get("name"),
                    "quantity":      -src_pkg_qty,
                    "volume_per":    src_vol_per,
                    "unit":          src_pkg_unit,
                    "total_volume":  round(-src_pkg_qty * src_vol_per, 4),
                    "location_id":   repack_location_id,
                    "location_name": repack_loc_name,
                    "received_at":   None,
                    "removed_at":    stamp_time,
                    "type":          "repackage_out",
                    "repack_group":  repack_group,
                    "notes":         notes,
                })
            for row in package_rows_parsed:
                pki_records.append({
                    "id":            generate_next_pki_id(pki_records),
                    "product_id":    str(product_id),
                    "package_id":    row["package_id"],
                    "package_name":  row["package_name"],
                    "quantity":      row["qty"],
                    "volume_per":    row["volume_per"],
                    "unit":          row["unit"],
                    "total_volume":  round(row["qty"] * row["volume_per"], 4),
                    "location_id":   repack_location_id,
                    "location_name": repack_loc_name,
                    "received_at":   stamp_time,
                    "type":          "repackage",
                    "repack_group":  repack_group,
                    "notes":         notes,
                })
            save_package_inventory(pki_records)

            # 3) Tanks
            if source_type == "package":
                source_label = f"{src_pkg_qty:g} x {src_pkg_def.get('name')}"
            elif repack_tank:
                source_label = repack_tank["name"]
            else:
                source_label = "loose stock"

            if repack_tank:
                apply_tank_issue(repack_tank["id"], prod, repack_gal, "gal", source="repackage",
                                 ref=repack_group, notes=notes or "Filled packages from tank")
            for trow, g in dest_tanks:
                apply_tank_receive(trow["id"], prod, g, "gal", source="repackage",
                                   ref=repack_group, notes=notes or ("Moved from " + source_label))

            # 4) Audit trail
            append_ledger_entry("repackage", {
                "repack_group":   repack_group,
                "product_id":     str(product_id),
                "product_name":   prod.get("name"),
                "location_id":    repack_location_id,
                "location":       chosen_loc,
                "source_type":    source_type,
                "source":         (
                    {"package_id": src_pkg_id, "package_name": src_pkg_def.get("name"), "qty": src_pkg_qty}
                    if source_type == "package"
                    else {"tank_id": repack_tank["id"], "tank_name": repack_tank["name"]} if repack_tank
                    else {"loose": True}
                ),
                "source_qty":     src_default,
                "packages_in":    [{"package_id": r["package_id"], "package_name": r["package_name"], "qty": r["qty"]}
                                   for r in package_rows_parsed],
                "tanks_in":       [{"tank_id": t["id"], "tank_name": t["name"], "gal": g} for t, g in dest_tanks],
                "filled_qty":     packaged_default_total,
                "loss_qty":       loss_default,
                "loss_value":     (loss_info or {}).get("issued_value", 0.0),
                "leftover_to_unpackaged": leftover_default,
                "unit":           default_unit,
                "by":             (current_user() or {}).get("username"),
                "notes":          notes,
            })

            # 5) Product notes + save (FIFO changed only if there was a loss)
            dest_label = ", ".join(
                [f"{row['qty']:g} x {row['package_name']}" for row in package_rows_parsed]
                + [f"{g:g} gal into {t['name']}" for t, g in dest_tanks]
            )
            still_unpackaged = round(max(
                0.0,
                (loc_on_hand - loss_default) - get_packaged_default_qty_for_location(prod, repack_location_id),
            ), 4)

            prod["last_updated"] = central_time_now_str()
            if notes:
                existing = (prod.get("notes") or "").strip()
                stamp = (
                    f"[Repackaged {source_label} into {dest_label} @ {stamp_time} | {chosen_loc} | {repack_group}"
                    + (f" | loss {loss_default:.4f} {default_unit}" if loss_default else "")
                    + "]"
                )
                prod["notes"] = (existing + "\n" + stamp + " " + notes).strip() if existing else (stamp + " " + notes)

            save_products(products)

            msg = f"Repackaged {prod.get('name')}: {source_label} → {dest_label}."
            if leftover_default > 0:
                msg += f" {leftover_default:.4f} {default_unit} left over went back to Unpackaged."
            if loss_default > 0:
                msg += f" Recorded {loss_default:.4f} {default_unit} loss."
            msg += f" Unpackaged at {chosen_loc}: {still_unpackaged:.4f} {default_unit}."
            flash(msg, "success")
            return redirect(next_url or url_for("inventory_adjust_page"))

        # -------------------------
        # ADD / REMOVE FLOW (UPDATED for location_id)
        # -------------------------
        receive_cost_raw = (request.form.get("receive_unit_cost") or "").strip()

        # HTML uses location_id for Receive + Remove
        location_id = (request.form.get("location_id") or "").strip() or None
        effective_location = loc_name_from_id(location_id) if location_id else None

        stage_flag = (request.form.get("stage") or "").lower() in ("1", "true", "yes", "on")
        customer = (request.form.get("customer") or "").strip() or None
        reason = (request.form.get("reason") or "").strip() or None
        scheduled_date = (request.form.get("scheduled_date") or "").strip() or None

        if not selling_by_package and unit not in ("gal", "lb", "unit"):
            errors.append("Unit must be gal, lb, or unit.")

        # require location for add/remove
        if action in ("add", "remove"):
            if not location_id:
                errors.append("Please select a location.")
            elif not loc_name_from_id(location_id):
                errors.append("Location not found.")

        qty_default = None
        package_rows_parsed = []
        package_breakdown_label = None
        tank_moves = []   # tank rows from the package list: [(tank_row, gallons)]

        if selling_by_package and not errors and prod:
            all_packages = load_packages()
            pkg_by_id = {str(pk.get("id")): pk for pk in all_packages}
            pkg_ids  = request.form.getlist("remove_package_id[]")
            pkg_qtys = request.form.getlist("remove_package_qty[]")

            # aggregate requested qty per package type (in case of duplicate rows)
            requested_by_pkg = {}
            for pid_raw, qraw in zip(pkg_ids, pkg_qtys):
                pid = (pid_raw or "").strip()
                qraw = (qraw or "").strip()
                if not pid or not qraw:
                    continue
                try:
                    pqty = float(qraw)
                except (ValueError, TypeError):
                    errors.append("Package quantity must be a number.")
                    continue
                if pqty <= 0:
                    continue
                requested_by_pkg[pid] = requested_by_pkg.get(pid, 0.0) + pqty

            if not requested_by_pkg and not errors:
                errors.append("Select at least one package type and quantity to sell/remove.")

            if not errors:
                avail_summary = get_package_inventory_summary(product_id)
                qty_default_total = 0.0
                label_parts = []

                for pid, pqty in requested_by_pkg.items():
                    if pid.startswith("tank:"):
                        trow = tank_at(location_id, pid[5:])
                        problem = tank_issue_problem(trow, product_id, pqty) if trow else "That tank isn't at the selected location."
                        if problem:
                            errors.append(problem)
                            continue
                        try:
                            qty_default_total += convert_to_product_default_unit(prod, pqty, "gal")
                        except Exception as e:
                            errors.append(str(e))
                            continue
                        tank_moves.append((trow, round(pqty, 4)))
                        label_parts.append(f"{pqty:g} gal out of {trow['name']}")
                        continue

                    pkg_def = pkg_by_id.get(pid)
                    if not pkg_def:
                        errors.append("Unknown package type selected.")
                        continue

                    available = float((avail_summary.get(pid) or {}).get("quantity", 0.0))
                    if pqty > available + 1e-9:
                        errors.append(
                            f"Not enough '{pkg_def.get('name')}' packaged for {prod.get('name')} — "
                            f"requested {pqty:g}, only {available:g} on hand."
                        )
                        continue

                    vol_per = float(pkg_def.get("volume") or 0.0)
                    pkg_unit = normalize_unit(pkg_def.get("unit") or "gal")
                    try:
                        row_default = convert_to_product_default_unit(prod, pqty * vol_per, pkg_unit)
                    except Exception as e:
                        errors.append(f"{pkg_def.get('name')}: {e}")
                        continue

                    qty_default_total += row_default
                    package_rows_parsed.append({
                        "package_id":   pid,
                        "package_name": pkg_def.get("name"),
                        "qty":          pqty,
                        "volume_per":   vol_per,
                        "unit":         pkg_unit,
                    })
                    label_parts.append(f"{pqty:g} x {pkg_def.get('name')}")

                if package_rows_parsed or tank_moves:
                    qty_default = round(qty_default_total, 4)
                    package_breakdown_label = ", ".join(label_parts)

        elif not errors and prod:
            try:
                qty_default = convert_to_product_default_unit(prod, qty, unit)
            except Exception as e:
                errors.append(str(e))

        recv_cost = None
        if action == "add":
            try:
                recv_cost = float(receive_cost_raw)
                if recv_cost < 0:
                    errors.append("Cost must be ≥ 0.")
            except ValueError:
                errors.append("Cost must be a number.")

        # ---- Tanks show up as "package" options (value "tank:<id>", amount in gallons) ----
        # Receive: rows can put gallons into tanks. Remove by package: rows can pull gallons out of tanks.
        chosen_tank, tank_gal = None, 0.0   # (kept for older forms that still send tank_id)
        if not errors and prod and action == "add":
            is_solid = (prod.get("phase") or "").lower() == "solid"
            pkg_by_id_chk = {str(pk.get("id")): pk for pk in load_packages()}
            packaged_gal_in = 0.0
            for pid_raw, q_raw in zip(request.form.getlist("package_id[]"), request.form.getlist("package_qty[]")):
                pid_raw = (pid_raw or "").strip()
                try:
                    n = float((q_raw or "0").strip() or 0)
                except ValueError:
                    n = 0.0
                if not pid_raw or n <= 0:
                    continue
                if pid_raw.startswith("tank:"):
                    trow = tank_at(location_id, pid_raw[5:])
                    if is_solid:
                        errors.append("Solid products can't go into tanks.")
                    elif not trow:
                        errors.append("That tank isn't at the selected location.")
                    else:
                        tank_moves.append((trow, round(n, 4)))
                else:
                    pk = pkg_by_id_chk.get(pid_raw)
                    if pk:
                        packaged_gal_in += package_volume_to_gallons(prod, n * float(pk.get("volume") or 0), pk.get("unit"))
            if tank_moves and not errors:
                try:
                    total_gal_in = gallons_from_input(qty, unit, prod)
                except ValueError as e:
                    errors.append(str(e))
                    total_gal_in = 0.0
                into_tanks = sum(g for _, g in tank_moves)
                if not errors and packaged_gal_in + into_tanks > total_gal_in + 0.01:
                    errors.append(f"Packages and tanks add up to {packaged_gal_in + into_tanks:g} gal, "
                                  f"but only {total_gal_in:g} gal is being received.")
                per_tank = {}
                for trow, g in tank_moves:
                    per_tank[trow["id"]] = per_tank.get(trow["id"], 0.0) + g
                for tid, g in per_tank.items():
                    problem = tank_receive_problem(next(t for t, _ in tank_moves if t["id"] == tid), product_id, g)
                    if problem:
                        errors.append(problem)

        if errors:
            return render_template(
                "inventory_adjust.html",
                app_title=APP_TITLE,
                errors=errors,
                products=products,
                staged=load_staging(),
                locations=locations,
                tanks_by_loc=tanks_by_loc,
                packages=load_packages(),
                form=dict(request.args)
            )

        # stage remove
        if action == "remove" and stage_flag:
            try:
                if selling_by_package:
                    stage_create(
                        products, product_id, qty_default, normalize_unit(prod.get("default_unit")),
                        customer, reason, scheduled_date, notes,
                        package_breakdown=package_rows_parsed,
                        location_id=location_id, location_name=effective_location,
                        tanks=[{"tank_id": trow["id"], "tank_name": trow.get("name"), "gal": g}
                               for trow, g in tank_moves] or None,
                    )
                else:
                    stage_create(products, product_id, qty, unit, customer, reason, scheduled_date, notes,
                                 location_id=location_id, location_name=effective_location)
            except StagingError as e:
                return render_template(
                    "inventory_adjust.html",
                    app_title=APP_TITLE,
                    errors=[str(e)],
                    products=products,
                    staged=load_staging(),
                    locations=locations,
                    tanks_by_loc=tanks_by_loc,
                    packages=load_packages(),
                    form=request.form,
                )

            if selling_by_package:
                if package_rows_parsed:
                    deduct_package_inventory(
                        product_id, package_rows_parsed, location_id, effective_location,
                        notes, ref_type="staged_sale",
                    )
                for trow, g in tank_moves:
                    # Product physically left the tank for the staging area
                    apply_tank_issue(trow["id"], prod, g, "gal", source="staged_remove", notes=notes)
                flash(f"Staged {prod.get('name')}: {package_breakdown_label}.", "success")

            return redirect(next_url or url_for("inventory_adjust_page"))

        # Ensure FIFO layers exist
        migrate_products_to_layers(products)
        _ensure_layers(prod)

        # Validate on-hand for location when removing
        if action == "remove":
            # compute on-hand at the chosen location
            chosen_loc = (effective_location or "UNASSIGNED").strip()
            loc_on_hand = 0.0
            for layer in (prod.get("layers") or []):
                if (layer.get("location") or "UNASSIGNED").strip().lower() == chosen_loc.lower():
                    loc_on_hand += float(layer.get("qty") or 0.0)

            if selling_by_package:
                # Availability for the specific packages being sold was
                # already validated above against packaged quantities;
                # this is just a sanity check against the location total.
                remove_limit = loc_on_hand
                limit_label = f"{loc_on_hand:.4f} on hand at that location"
            else:
                # Plain bulk removal (straight from the tank/pile, not a
                # package) can only draw from what's actually still loose —
                # gallons already sitting in packages aren't available here.
                already_packaged_default = get_packaged_default_qty_for_location(prod, location_id)
                remove_limit = max(0.0, loc_on_hand - already_packaged_default)
                limit_label = (
                    f"{remove_limit:.4f} Unpackaged on hand at that location "
                    f"({loc_on_hand:.4f} total, {already_packaged_default:.4f} already packaged)"
                )
                if not chosen_tank:
                    in_tanks = product_tank_gal(product_id, location_id)
                    if in_tanks > 0:
                        try:
                            in_tanks_default = convert_to_product_default_unit(prod, in_tanks, "gal")
                        except Exception:
                            in_tanks_default = 0.0
                        remove_limit = max(0.0, remove_limit - in_tanks_default)
                        limit_label = (
                            f"{remove_limit:.4f} loose at that location ({in_tanks:g} gal is in tanks, "
                            f"so to take it out of a tank, choose Package type and pick the tank)"
                        )

            if qty_default > remove_limit + 1e-9:
                return render_template(
                    "inventory_adjust.html",
                    app_title=APP_TITLE,
                    errors=[f"Cannot remove {qty_default:.4f} {prod.get('default_unit')} from {chosen_loc} — only {limit_label}."],
                    products=products,
                    staged=load_staging(),
                    locations=locations,
                    tanks_by_loc=tanks_by_loc,
                    packages=load_packages(),
                    form=request.form,
                )

            # remove FIFO from the chosen location
            try:
                fifo_issue_from_location(prod, qty_default, chosen_loc)
            except Exception as e:
                return render_template(
                    "inventory_adjust.html",
                    app_title=APP_TITLE,
                    errors=[str(e)],
                    products=products,
                    staged=load_staging(),
                    locations=locations,
                    tanks_by_loc=tanks_by_loc,
                    packages=load_packages(),
                    form=request.form,
                )

            if selling_by_package:
                if package_rows_parsed:
                    deduct_package_inventory(
                        product_id, package_rows_parsed, location_id, effective_location, notes,
                    )
                for trow, g in tank_moves:
                    apply_tank_issue(trow["id"], prod, g, "gal", source="remove", notes=notes)
                flash(f"Removed {prod.get('name')} from {chosen_loc}: {package_breakdown_label}.", "success")

            verb = "Removed"
            sign = "-"
        else:
            # receive into chosen location
            fifo_receive(prod, qty_default, recv_cost, location=effective_location)
            _sync_product_qty_and_avg_cost_from_layers(prod)

            # ---- Package inventory records (multiple rows, optional) ----
            pkg_ids  = request.form.getlist("package_id[]")
            pkg_qtys = request.form.getlist("package_qty[]")
            if pkg_ids:
                all_packages  = load_packages()
                pki_records   = load_package_inventory()
                pkg_by_id     = {str(pk.get("id")): pk for pk in all_packages}
                changed       = False

                for pkg_id_raw, pkg_qty_raw in zip(pkg_ids, pkg_qtys):
                    pkg_id  = (pkg_id_raw  or "").strip()
                    pkg_qty_str = (pkg_qty_raw or "").strip()
                    if not pkg_id or not pkg_qty_str:
                        continue
                    try:
                        pkg_qty = float(pkg_qty_str)
                        if pkg_qty <= 0:
                            continue
                    except (ValueError, TypeError):
                        continue

                    pkg_def = pkg_by_id.get(pkg_id)
                    if not pkg_def:
                        continue

                    pki_records.append({
                        "id":            generate_next_pki_id(pki_records),
                        "product_id":    str(product_id),
                        "package_id":    pkg_id,
                        "package_name":  pkg_def.get("name"),
                        "quantity":      pkg_qty,
                        "volume_per":    float(pkg_def.get("volume") or 0.0),
                        "unit":          pkg_def.get("unit") or "gal",
                        "total_volume":  pkg_qty * float(pkg_def.get("volume") or 0.0),
                        "location_id":   location_id,
                        "location_name": effective_location,
                        "received_at":   now_central_iso(),
                        "notes":         notes,
                    })
                    changed = True

                if changed:
                    save_package_inventory(pki_records)

            for trow, g in tank_moves:
                apply_tank_receive(trow["id"], prod, g, "gal", source="receive", notes=notes)
            if tank_moves:
                flash(f"Received {prod.get('name')}: " + ", ".join(f"{g:g} gal into {t['name']}" for t, g in tank_moves) + ".",
                      "success")

            verb = "Received"
            sign = "+"

        prod["last_updated"] = central_time_now_str()

        if notes:
            existing = (prod.get("notes") or "").strip()
            qty_label = package_breakdown_label if selling_by_package else f"{qty} {unit}"
            stamp = f"[{verb} {qty_label} ({sign}{qty_default:.4f} {prod.get('default_unit','')}) @ {now_central_iso()} | {effective_location}]"
            prod["notes"] = (existing + "\n" + stamp + " " + notes).strip() if existing else (stamp + " " + notes)

        save_products(products)
        return redirect(next_url or url_for("inventory_adjust_page"))

    # -------------------------
    # GET
    # -------------------------
    try:
        formulas = load_formulas()
    except Exception:
        formulas = []
    formulas.sort(key=lambda f: (f.get("updated_at") or f.get("created_at") or ""), reverse=True)

    # Allow deep-linking in from Live Inventory with a product/location
    # pre-selected, e.g. /inventory/adjust?product_id=...&location_id=...
    prefill_form = {}
    if request.args.get("product_id"):
        prefill_form["product_id"] = request.args.get("product_id")
    if request.args.get("location_id"):
        prefill_form["location_id"] = request.args.get("location_id")

    return render_template(
        "inventory_adjust.html",
        app_title=APP_TITLE,
        errors=None,
        products=products,
        staged=load_staging(),
        locations=locations,
        tanks_by_loc=tanks_by_loc,
        packages=load_packages(),
        formulas=formulas,
        form=prefill_form,
    )




@app.route("/inventory/live")
def live_inventory_page():
    locations = load_locations_for_user()
    return render_template(
        "live_inventory.html",
        app_title=APP_TITLE,
        locations=locations,
        packages=load_packages(),
    )


@app.route("/inventory/add", methods=["GET", "POST"])
def inventory_add_page():
    if request.method == "POST":
        return inventory_adjust_page()
    return redirect(url_for("inventory_adjust_page"))


# -------------------------
# Staging routes
# -------------------------
@app.route("/staging/create", methods=["POST"])
def staging_create_route():
    data = request.get_json(silent=True) if request.is_json else request.form
    product_id = (data.get("product_id") or "").strip()
    qty = data.get("qty") or data.get("quantity") or 0
    unit = normalize_unit((data.get("unit") or "gal").lower())
    customer = data.get("customer")
    reason = data.get("reason")
    scheduled_date = data.get("scheduled_date")
    notes = data.get("notes")
    location_id = str(data.get("location_id") or "").strip()
    loc = get_location_by_id(load_locations_for_user(), location_id) if location_id else None
    if not loc:
        return {"ok": False, "errors": ["Please select a location."]}, 400

    products = load_products()
    try:
        rec = stage_create(products, product_id, qty, unit, customer, reason, scheduled_date, notes,
                           location_id=loc["id"], location_name=loc.get("name"))
    except StagingError as e:
        return {"ok": False, "errors": [str(e)]}, 400
    return {"ok": True, "record": rec}, 200


@app.route("/staging/release/<record_id>", methods=["GET", "POST"])
def staging_release_flow(record_id):
    records = load_staging()
    rec = next((r for r in records if r.get("id") == record_id), None)
    if not rec:
        return render_template(
            "staging_release.html",
            app_title=APP_TITLE,
            error="Staging record not found.",
            record=None,
            form={},
        ), 404

    if request.method == "GET":
        return render_template("staging_release.html", app_title=APP_TITLE, error=None, record=rec, form={})

    confirm = (request.form.get("confirm") or "").lower()
    if confirm != "yes":
        return redirect(url_for("inventory_adjust_page"))

    ship_date = (request.form.get("ship_date") or "").strip()
    ship_time = (request.form.get("ship_time") or "").strip()
    carrier = (request.form.get("carrier") or "").strip()

    try:
        stage_release(record_id)
    except StagingError as e:
        return render_template(
            "staging_release.html",
            app_title=APP_TITLE,
            error=str(e),
            record=rec,
            form=request.form,
        ), 400

    records = load_staging()
    for r in records:
        if r.get("id") == record_id:
            r["released_carrier"] = carrier or None
            r["released_date"] = ship_date or None
            r["released_time"] = ship_time or None
            save_staging(records)
            break

    return redirect(url_for("inventory_adjust_page"))


@app.route("/staging/void/<record_id>", methods=["POST"])
def staging_void_route(record_id):
    return_flag = (request.form.get("return_to_inventory") or request.args.get("return_to_inventory") or "").lower()
    return_to_inventory = return_flag in ("1", "true", "yes", "on")
    try:
        rec = stage_void(record_id, return_to_inventory=return_to_inventory)
    except StagingError as e:
        return {"ok": False, "errors": [str(e)]}, 400
    return {"ok": True, "record": rec}, 200


def _staging_row(rec):
    """Shape one staged record for the Staging page."""
    q = _safe_float(rec.get("qty_default"), 0.0)
    u = normalize_unit(rec.get("default_unit") or "gal")
    w = _safe_float(rec.get("weight_snapshot"), 0.0)
    gal = lb = units = None
    if u == "gal":
        gal, lb = q, (q * w if w > 0 else None)
    elif u == "lb":
        lb, gal = q, (q / w if w > 0 else None)
    else:
        units = q

    pkgs = [f"{_safe_float(p.get('qty'), 0):g} × {p.get('package_name') or 'Package'}"
            for p in (rec.get("packages") or [])]
    pkgs += [f"{_safe_float(t.get('gal'), 0):g} GAL from {t.get('tank_name') or 'tank'}"
             for t in (rec.get("tanks") or [])]

    # Days in staging, counted in Central time (0 = staged today)
    today = datetime.now(tz=CENTRAL_TZ).date()
    try:
        staged_day = datetime.fromisoformat(str(rec.get("staged_at") or "").replace("Z", "")).date()
        days = max(0, (today - staged_day).days)
    except ValueError:
        days = None

    lift = rec.get("expected_lift_date") or rec.get("scheduled_date") or ""
    try:
        lift_day = datetime.strptime(lift, "%Y-%m-%d").date()
    except (TypeError, ValueError):
        lift, lift_day = "", None

    return {
        "id": rec.get("id"),
        "staged_at": rec.get("staged_at"),
        "days": days,
        "lift_date": lift,
        "lift_overdue": bool(lift_day and lift_day < today),
        "value": _safe_float(rec.get("fifo_issued_value", rec.get("value_snapshot")), 0.0),
        "product_name": rec.get("product_name") or "—",
        "gal": gal, "lb": lb, "units": units,
        "packages": pkgs,
        "customer": rec.get("customer"),
        "notes": rec.get("notes"),
        "scheduled_date": rec.get("scheduled_date"),
    }


def _staging_record_location_ok(rec) -> bool:
    user = current_user()
    if rec.get("location_id"):
        return user_can_use_location(user, loc_id=rec.get("location_id"))
    if rec.get("location_name"):
        return user_can_use_location(user, loc_name=rec.get("location_name"))
    return allowed_location_ids(user) is None   # old records with no location: unrestricted users only


@app.route("/staging")
def staging_page():
    locations = load_locations_for_user()
    by_id = {str(l.get("id")): l for l in locations}
    by_name = {(l.get("name") or "").strip().lower(): str(l.get("id")) for l in locations}

    groups = {str(l.get("id")): [] for l in locations}
    unassigned = []
    for rec in load_staging():
        if (rec.get("status") or "").lower() != "staged":
            continue
        lid = str(rec.get("location_id") or "") or by_name.get((rec.get("location_name") or "").strip().lower(), "")
        if lid in groups:
            groups[lid].append(_staging_row(rec))
        elif not rec.get("location_id") and not rec.get("location_name") and allowed_location_ids(current_user()) is None:
            unassigned.append(_staging_row(rec))

    sections = []
    for lid, rows in groups.items():
        rows.sort(key=lambda x: x.get("staged_at") or "")
        sections.append({
            "id": lid,
            "name": by_id[lid].get("name") or lid,
            "rows": rows,
            "total_gal": round(sum(r["gal"] or 0 for r in rows), 2),
            "total_value": round(sum(r["value"] for r in rows), 2),
        })
    sections.sort(key=lambda x: (len(x["rows"]) == 0, (x["name"] or "").lower()))
    # One-location view (the Staging tab on a location's page)
    only = (request.args.get("location_id") or "").strip()
    if only:
        sections = [sec for sec in sections if sec["id"] == only]
        unassigned = []

    if unassigned:
        unassigned.sort(key=lambda x: x.get("staged_at") or "")
        sections.append({"id": "none", "name": "No location recorded", "rows": unassigned,
                         "total_gal": round(sum(r["gal"] or 0 for r in unassigned), 2),
                         "total_value": round(sum(r["value"] for r in unassigned), 2)})

    return render_template("staging.html", app_title=APP_TITLE, sections=sections,
                           open_id=only or request.args.get("open", ""), only_location=only,
                           embed=request.args.get("embed") == "1")


def _staging_action(record_id, action):
    rec = next((r for r in load_staging() if r.get("id") == record_id), None)
    back = request.form.get("open") or ""
    only = (request.form.get("only_location") or "").strip()
    embed = "1" if request.form.get("embed") == "1" else None

    def back_to_staging():
        # Return to the same view the button was pressed in (full list, or one location's tab)
        return redirect(url_for("staging_page", open=back or None, location_id=only or None, embed=embed))

    if not rec:
        flash("That staging order wasn't found. It may have already been handled.", "danger")
        return back_to_staging()
    if not _staging_record_location_ok(rec):
        return render_template("no_access.html", message="You aren't assigned to that location."), 403
    try:
        if action == "picked_up":
            stage_release(record_id)
            flash(f"{rec.get('product_name')} marked as picked up.", "success")
        else:
            done = stage_void(record_id, return_to_inventory=True)
            flash(f"Order canceled. {rec.get('product_name')} is back in inventory"
                  f"{' at ' + rec['location_name'] if rec.get('location_name') else ''}.", "success")
            for w in (done.get("cancel_warnings") or []):
                flash(w, "warning")
    except StagingError as e:
        flash(str(e), "danger")
    return back_to_staging()


@app.route("/staging/<record_id>/lift-date", methods=["POST"])
def staging_lift_date(record_id):
    """Save (or clear) the expected lift date on a staged order. Called by the page as you pick a date."""
    data = request.get_json(silent=True) if request.is_json else request.form
    raw = ((data or {}).get("lift_date") or "").strip()
    if raw:
        try:
            datetime.strptime(raw, "%Y-%m-%d")
        except ValueError:
            return {"ok": False, "error": "Pick a valid date."}, 400

    records = load_staging()
    rec = next((r for r in records if r.get("id") == record_id), None)
    if not rec or (rec.get("status") or "").lower() != "staged":
        return {"ok": False, "error": "That order is no longer in staging. Refresh the page."}, 404
    if not _staging_record_location_ok(rec):
        return {"ok": False, "error": "You aren't assigned to that location."}, 403

    rec["expected_lift_date"] = raw or None
    rec["scheduled_date"] = raw or None      # keep the older field in sync
    save_staging(records)
    today = datetime.now(tz=CENTRAL_TZ).date()
    overdue = bool(raw) and datetime.strptime(raw, "%Y-%m-%d").date() < today
    return {"ok": True, "lift_date": raw, "overdue": overdue}, 200


@app.route("/staging/<record_id>/picked-up", methods=["POST"])
def staging_picked_up(record_id):
    return _staging_action(record_id, "picked_up")


@app.route("/staging/<record_id>/cancel", methods=["POST"])
def staging_cancel(record_id):
    return _staging_action(record_id, "cancel")


# -------------------------
# Blend Builder routes (JSON first)
# -------------------------
@app.route("/blend/builder", methods=["GET"])
def blend_builder_info():
    products = load_products()
    return {
        "ok": True,
        "products": [
            {
                "id": p["id"],
                "name": p["name"],
                "default_unit": p.get("default_unit"),
                "weight": p.get("weight"),
                "package_size_gal": p.get("package_size_gal"),
                "on_hand": p.get("quantity"),
            }
            for p in products
        ],
        "modes": ["percent", "absolute"],
    }



@app.route("/blend/build", methods=["POST"])
def blend_build():
    if request.is_json:
        payload = request.get_json(silent=True) or {}
        name = (payload.get("name") or "").strip()
        target_unit = normalize_unit((payload.get("target_unit") or "gal").lower())
        mode = (payload.get("mode") or "percent").lower()
        try:
            target_qty = float(payload.get("target_qty") or 0.0)
        except ValueError:
            target_qty = 0.0
        components = payload.get("components") or []
    else:
        name = (request.form.get("name") or "").strip()
        target_unit = normalize_unit((request.form.get("target_unit") or "gal").lower())
        mode = (request.form.get("mode") or "percent").lower()
        try:
            target_qty = float(request.form.get("target_qty") or 0.0)
        except ValueError:
            target_qty = 0.0

        components = []
        if isinstance(request.form.get("components"), str):
            try:
                components = json.loads(request.form.get("components"))
            except Exception:
                components = []

        if not components:
            pids = request.form.getlist("product_id[]") or request.form.getlist("product_id")
            if mode == "percent":
                pcts = request.form.getlist("percent[]") or request.form.getlist("percent")
                for pid, pct in zip(pids, pcts):
                    try:
                        v = float(pct)
                    except (TypeError, ValueError):
                        v = 0.0
                    if pid and v > 0:
                        components.append({"product_id": pid, "percent": v})
            else:
                qtys = request.form.getlist("qty[]") or request.form.getlist("qty")
                units = request.form.getlist("qty_unit[]") or request.form.getlist("qty_unit")
                for pid, q_raw, u in zip(pids, qtys, units):
                    try:
                        q = float(q_raw)
                    except (TypeError, ValueError):
                        q = 0.0
                    u = normalize_unit((u or "gal").lower())
                    if pid and q > 0:
                        components.append({"product_id": pid, "qty": q, "qty_unit": u})

    if not name:
        return {"ok": False, "errors": ["Blend name is required."]}, 400

    products = load_products()

    # default: EXECUTE (consume inventory + receive finished blend)
    # You can turn it off by sending {"execute": false} if you want a "quote-only" mode later.
    execute_flag = True

    if request.is_json:
        payload = request.get_json(silent=True) or {}
        execute_flag = bool(payload.get("execute", True))
        location_id = str(payload.get("location_id") or "").strip()
    else:
        execute_flag = (request.form.get("execute") or "true").lower() in ("1","true","yes","on")
        location_id = (request.form.get("location_id") or "").strip()

    # The finished blend is received into the location picked on the page.
    loc = get_location_by_id(load_locations_for_user(), location_id) if location_id else None
    if not loc:
        return {"ok": False, "errors": ["Please select a location."]}, 400
    location = (loc.get("name") or "").strip() or str(loc.get("id"))

    try:
        if execute_flag:
            result = execute_builder_blend(products, name, target_qty, target_unit, mode, components,
                                           location=location, location_id=location_id)
            new_id = result["blend_product"]["id"]
        else:
            result = build_blend(products, name, target_qty, target_unit, mode, components, location=location)
            new_id = result["new_product"]["id"]
    except BlendError as e:
        return {"ok": False, "errors": [str(e)]}, 400
    except Exception as e:
        return {"ok": False, "errors": [f"Blend failed: {e}"]}, 400

    save_products(products)

    if (request.args.get("redirect") == "1") and not request.is_json:
        return redirect(url_for("product_detail", product_id=new_id))

    return {"ok": True, "new_product_id": new_id, "result": result}, 200

@app.get("/api/formulas")
def api_formulas_list():
    formulas = load_formulas()
    formulas.sort(key=lambda x: x.get("updated_at", ""), reverse=True)
    return {"ok": True, "formulas": formulas}, 200


@app.get("/api/formulas/<formula_id>")
def api_formulas_get(formula_id):
    formulas = load_formulas()
    f = get_formula_by_id(formulas, formula_id)
    if not f:
        return {"ok": False, "errors": ["Formula not found."]}, 404
    return {"ok": True, "formula": f}, 200
@app.get("/formulas/<formula_id>")
def formulas_info_page(formula_id):
    formulas = load_formulas()
    f = get_formula_by_id(formulas, formula_id)
    if not f:
        flash("Formula not found.", "danger")
        return redirect(url_for("formulas_page"))

    products = load_products()
    products_simple = [{"id": p["id"], "name": p["name"]} for p in products if p.get("id")]

    return render_template(
        "formula_information.html",
        app_title=APP_TITLE,
        products=products_simple,
        form=f,
    )



@app.route("/blend/new")
def blend_new_page():
    # Load formulas for the bottom “Formula Library” section
    try:
        formulas = load_formulas()
    except Exception:
        formulas = []

    # newest first (uses updated_at if present)
    formulas.sort(key=lambda f: (f.get("updated_at") or f.get("created_at") or ""), reverse=True)

    return render_template(
        "blend_builder.html",
        app_title=APP_TITLE,
        formulas=formulas,
        selected_formula_id=request.args.get("formula", ""),
        locations=load_locations_for_user(),
    )


@app.get("/formulas/new")
def formulas_new_page():
    products = load_products()
    # keep payload light for dropdown
    products_simple = [{"id": p["id"], "name": p["name"]} for p in products if p.get("id")]
    return render_template(
        "formula_builder.html",
        app_title=APP_TITLE,
        products=products_simple,
        form={}
    )

@app.post("/formulas/create_percent")
def formulas_create_percent():
    name = (request.form.get("name") or "").strip()
    description = (request.form.get("description") or "").strip() or None

    target_unit = normalize_unit((request.form.get("target_unit") or "gal").lower())
    try:
        target_qty = float(request.form.get("target_qty") or 0.0)
    except Exception:
        target_qty = 0.0

    if not name:
        flash("Formula name is required.", "danger")
        return redirect(url_for("formulas_new_page"))

    if target_unit not in ("gal", "lb"):
        flash("Target unit must be GAL or LB.", "danger")
        return redirect(url_for("formulas_new_page"))

    # Parse arrays
    pids = request.form.getlist("product_id[]")
    pcts = request.form.getlist("percent[]")

    components = []
    for pid, pct_raw in zip(pids, pcts):
        pid = (pid or "").strip()
        try:
            pct = float(pct_raw or 0.0)
        except Exception:
            pct = 0.0
        if pid and pct > 0:
            components.append({"product_id": pid, "percent": pct})

    if not components:
        flash("Add at least one product with a percent.", "danger")
        return redirect(url_for("formulas_new_page"))

    total_pct = sum(float(c["percent"]) for c in components)
    if abs(total_pct - 100.0) > 0.001:
        flash(f"Percents must sum to 100%. Current total: {total_pct:.3f}%.", "danger")
        return redirect(url_for("formulas_new_page"))

    now = now_central_iso()
    formulas = load_formulas()

    # compute lb/gal snapshot (optional)
    products = load_products()
    by_id = index_products_by_id(products)
    rows = []
    for c in components:
        prod = by_id.get(c["product_id"])
        if not prod:
            continue
        required_in_batch_unit = (float(c["percent"]) / 100.0) * 1.0  # 1 gal basis
        q_prod, unit_str, vol_gal = convert_required_to_product_unit(prod, required_in_batch_unit, "gal")
        rows.append({"product": prod, "vol_gal": float(vol_gal), "required_qty_in_product_unit": q_prod})

    lb_per_gal_est = None
    try:
        if rows:
            lb_per_gal_est = round(float(compute_weighted_lb_per_gal(rows)), 6)
    except Exception:
        lb_per_gal_est = None


    rec = {
        "id": str(uuid.uuid4()),
        "name": name,
        "description": description,
        "mode": "percent",
        "defaults": {
            "target_qty": (target_qty if target_qty > 0 else None),
            "target_unit": target_unit,
        },
        "components": components,
        "tags": [],
        "created_at": now,
        "updated_at": now,
        "lb_per_gal_estimate": lb_per_gal_est,
    }

    formulas.append(rec)
    save_formulas(formulas)

    flash("Formula saved.", "success")
    return redirect(url_for("formulas_page"))

@app.post("/formulas/save_from_blend")
def formulas_save_from_blend():
    payload = request.get_json(silent=True) or {}

    name = (payload.get("name") or "").strip()
    description = (payload.get("description") or "").strip() or None
    mode = (payload.get("mode") or "percent").lower()
    target_unit = normalize_unit((payload.get("target_unit") or "gal").lower())
    try:
        target_qty = float(payload.get("target_qty") or 0.0)
    except Exception:
        target_qty = 0.0

    components = payload.get("components") or []

    if not name:
        return {"ok": False, "errors": ["Formula name is required."]}, 400
    if mode not in ("percent", "absolute"):
        return {"ok": False, "errors": ["Mode must be 'percent' or 'absolute'."]}, 400
    if target_unit not in ("gal", "lb"):
        return {"ok": False, "errors": ["target_unit must be 'gal' or 'lb'."]}, 400

    # Basic component validation (lightweight)
    cleaned = []
    for c in components:
        pid = (c.get("product_id") or "").strip()
        if not pid:
            continue

        if mode == "percent":
            try:
                pct = float(c.get("percent") or 0.0)
            except Exception:
                pct = 0.0
            if pct > 0:
                cleaned.append({"product_id": pid, "percent": pct})
        else:
            try:
                qty = float(c.get("qty") or 0.0)
            except Exception:
                qty = 0.0
            u = normalize_unit((c.get("qty_unit") or "gal").lower())
            if qty > 0:
                cleaned.append({"product_id": pid, "qty": qty, "qty_unit": u})

    if not cleaned:
        return {"ok": False, "errors": ["Add at least one valid component."]}, 400

    now = now_central_iso()
    formulas = load_formulas()

    rec = {
        "id": str(uuid.uuid4()),
        "name": name,
        "description": description,
        "mode": mode,
        "defaults": {
            "target_qty": target_qty if target_qty > 0 else None,
            "target_unit": target_unit,
        },
        "components": cleaned,
        "tags": payload.get("tags") or [],
        "created_at": now,
        "updated_at": now,
    }

    formulas.append(rec)
    save_formulas(formulas)

    return {"ok": True, "formula_id": rec["id"], "formula": rec}, 200

@app.get("/api/blend/plan")
def api_blend_plan():
    """What each component needs for this batch and what's on hand at the location."""
    formula = get_formula_by_id(load_formulas(), (request.args.get("formula_id") or "").strip())
    loc = get_location_by_id(load_locations_for_user(), (request.args.get("location_id") or "").strip())
    if not loc:
        return jsonify({"ok": False, "errors": ["Pick a location."]}), 400
    products = load_products()
    try:
        rows = plan_formula_requirements(products, formula, request.args.get("batch_qty") or 0,
                                         request.args.get("batch_unit") or "gal", allow_zero=True)
    except SourcingError as e:
        return jsonify({"ok": False, "errors": [str(e)]}), 400
    out = []
    for r in rows:
        stock = location_stock_for_product(r["product"], loc["id"], loc["name"])
        out.append({"product_id": r["product_id"], "name": r["name"], "percent": r["percent"],
                    "needed_gal": r["needed_gal"], **stock})
    blend_name_lc = (formula.get("name") or "").strip().lower()
    blend_pid = next((str(p.get("id")) for p in products if (p.get("name") or "").strip().lower() == blend_name_lc), None)
    out_tanks = [{"id": t["id"], "name": t["name"], "free_gal": t["free_gal"], "fill_gal": t["fill_gal"],
                  "product_name": t["product_name"]}
                 for t in tank_rows_for_location(loc["id"])
                 if t["product_id"] in (None, blend_pid)]
    return jsonify({"ok": True, "location": loc["name"], "components": out, "out_tanks": out_tanks,
                    "total_gal": round(sum(r["needed_gal"] for r in rows), 4),
                    "package_types": [{"id": str(p.get("id")), "name": p.get("name"),
                                       "volume_gal": float(p.get("volume") or 0),
                                       "fillable": normalize_unit(p.get("unit") or "gal") == "gal"}
                                      for p in load_packages()]})


@app.post("/api/blend/validate")
def api_blend_validate():
    """Check a blend exactly the way Execute will, without changing anything."""
    f = request.form
    formula = get_formula_by_id(load_formulas(), (f.get("formula_id") or "").strip())
    if not formula:
        return jsonify({"ok": False, "errors": ["Pick a formula."]})
    loc = get_location_by_id(load_locations_for_user(), (f.get("location_id") or "").strip())
    if not loc:
        return jsonify({"ok": False, "errors": ["Pick the location where the blend is being made."]})
    products = load_products()
    migrate_products_to_layers(products)
    try:
        execute_sourced_formula_blend(products, formula, f.get("batch_qty"),
                                      normalize_unit((f.get("batch_unit") or "gal").lower()),
                                      loc["id"], loc["name"], f, dry_run=True)
    except SourcingError as e:
        return jsonify({"ok": False, "errors": e.errors})
    except (BlendError, ValueError) as e:
        return jsonify({"ok": False, "errors": [str(e)]})
    return jsonify({"ok": True})


@app.post("/blend/execute_formula")
def blend_execute_formula():
    formula_id = (request.form.get("formula_id") or "").strip()
    batch_unit = normalize_unit((request.form.get("batch_unit") or "gal").lower())
    batch_qty = request.form.get("batch_qty")
    notes = (request.form.get("notes") or "").strip() or None
    location_id = (request.form.get("location_id") or "").strip()

    back = url_for("blend_new_page", formula=formula_id)
    formula = get_formula_by_id(load_formulas(), formula_id)
    if not formula:
        flash("Formula not found.", "danger")
        return redirect(back)
    loc = get_location_by_id(load_locations_for_user(), location_id)
    if not loc:
        flash("Pick the location where the blend is being made.", "danger")
        return redirect(back)

    products = load_products()
    migrate_products_to_layers(products)
    try:
        entry = execute_sourced_formula_blend(
            products, formula, batch_qty, batch_unit, loc["id"], loc["name"], request.form,
            notes=notes, username=(current_user() or {}).get("username"),
        )
    except SourcingError as e:
        for msg in e.errors:
            flash(msg, "danger")
        return redirect(back)
    except (BlendError, ValueError) as e:
        flash(str(e), "danger")
        return redirect(back)

    save_products(products)
    msg = f"Blend #{entry['number']} done: {entry['total_gal']:g} GAL of {entry['blend']} at {entry['location']}."
    if entry["packaged"]:
        msg += " Packaged into " + ", ".join(f"{p['qty']} x {p['package_name']}" for p in entry["packaged"]) + "."
    if entry.get("out_tank"):
        msg += f" {entry['out_tank']['gal']:g} gal went into {entry['out_tank']['name']}."
    over = sum(c["overage_gal"] for c in entry["components"])
    if over > 0:
        msg += f" Overage logged: {over:g} GAL" + (f" (${entry['overage_cost']:.2f})." if can_see_costs() else ".")
    flash(msg, "success")
    return redirect(url_for("blend_log_page", highlight=entry["number"]))


@app.get("/blend/log")
def blend_log_page():
    """Every executed blend, one row per component, like the Blend Log sheet."""
    allowed = allowed_location_ids(current_user())
    log = [b for b in load_blends() if allowed is None or str(b.get("location_id")) in allowed]
    log.sort(key=lambda b: int(b.get("number") or 0), reverse=True)
    pkg_names = [p.get("name") for p in load_packages()]
    return render_template("blend_log.html", app_title=APP_TITLE, log=log, pkg_names=pkg_names,
                           highlight=request.args.get("highlight", type=int))


@app.route("/blend/execute_at_location", methods=["POST"])
def blend_execute_at_location():
    """
    Executes a blend from the Inventory Adjust page's "Blend" tab.
    Unlike the standalone Blend Builder (which pulls ingredients from
    wherever in inventory, oldest layer first), this is location-scoped:
    ingredients are drawn only from the selected location's FIFO layers,
    and the finished blend is received back into that same location —
    matching how Receive/Remove/Move/Repackage all work on this page.

    Supports both:
      - blend_mode=formula  -> execute a saved formula
      - blend_mode=custom   -> build one off (percent or absolute mode)

    Optionally, part (or all) of the finished blend can be packaged
    directly (blend_package_id[] / blend_package_qty[]), same as the
    Repackage tab — this does not remove anything from the total, it just
    records that portion as already sitting in packages.
    """
    next_url = (request.form.get("next") or "").strip()
    blend_mode = (request.form.get("blend_mode") or "custom").strip().lower()

    locations = load_locations_safe()
    location_id = (request.form.get("location_id") or "").strip() or None
    loc = get_location_by_id(locations, location_id) if location_id else None
    location_name = (loc or {}).get("name")

    notes = (request.form.get("notes") or "").strip() or None

    errors = []
    if not location_id:
        errors.append("Please select a location.")
    elif not location_name:
        errors.append("Location not found.")

    # ---- Parse optional "package the finished blend" rows ----
    all_packages = load_packages()
    pkg_by_id = {str(pk.get("id")): pk for pk in all_packages}
    pkg_ids  = request.form.getlist("blend_package_id[]")
    pkg_qtys = request.form.getlist("blend_package_qty[]")

    package_rows_parsed = []
    for pid_raw, qraw in zip(pkg_ids, pkg_qtys):
        pid = (pid_raw or "").strip()
        qraw = (qraw or "").strip()
        if not pid or not qraw:
            continue
        try:
            pqty = float(qraw)
        except (ValueError, TypeError):
            errors.append("Package quantity must be a number.")
            continue
        if pqty <= 0:
            continue
        pkg_def = pkg_by_id.get(pid)
        if not pkg_def:
            errors.append("Unknown package type selected.")
            continue
        package_rows_parsed.append({
            "package_id":   pid,
            "package_name": pkg_def.get("name"),
            "qty":          pqty,
            "volume_per":   float(pkg_def.get("volume") or 0.0),
            "unit":         normalize_unit(pkg_def.get("unit") or "gal"),
        })

    if errors:
        for e in errors:
            flash(e, "danger")
        return redirect(next_url or url_for("inventory_adjust_page"))

    products = load_products()

    try:
        if blend_mode == "formula":
            formula_id = (request.form.get("formula_id") or "").strip()
            batch_unit = normalize_unit((request.form.get("batch_unit") or "gal").lower())
            try:
                batch_qty = float(request.form.get("batch_qty") or 0.0)
            except ValueError:
                batch_qty = 0.0

            formulas = load_formulas()
            formula = get_formula_by_id(formulas, formula_id)
            if not formula:
                raise BlendError("Formula not found.")

            result = execute_formula_blend(
                products, formula, batch_qty, batch_unit,
                location=location_name,
                consume_from_location_only=True,
                location_id=location_id,
                package_rows=package_rows_parsed or None,
                notes=notes,
            )
        else:
            name = (request.form.get("name") or "").strip()
            target_unit = normalize_unit((request.form.get("target_unit") or "gal").lower())
            mode = (request.form.get("mode") or "percent").lower()
            try:
                target_qty = float(request.form.get("target_qty") or 0.0)
            except ValueError:
                target_qty = 0.0

            pids = request.form.getlist("product_id[]")
            components = []
            if mode == "percent":
                pcts = request.form.getlist("percent[]")
                for pid, pct_raw in zip(pids, pcts):
                    try:
                        v = float(pct_raw)
                    except (TypeError, ValueError):
                        v = 0.0
                    if pid and v > 0:
                        components.append({"product_id": pid, "percent": v})
            else:
                qtys  = request.form.getlist("qty[]")
                units = request.form.getlist("qty_unit[]")
                for pid, q_raw, u in zip(pids, qtys, units):
                    try:
                        q = float(q_raw)
                    except (TypeError, ValueError):
                        q = 0.0
                    u = normalize_unit((u or "gal").lower())
                    if pid and q > 0:
                        components.append({"product_id": pid, "qty": q, "qty_unit": u})

            result = execute_builder_blend(
                products, name, target_qty, target_unit, mode, components,
                location=location_name,
                consume_from_location_only=True,
                location_id=location_id,
                package_rows=package_rows_parsed or None,
                notes=notes,
            )
    except BlendError as e:
        flash(str(e), "danger")
        return redirect(next_url or url_for("inventory_adjust_page"))
    except Exception as e:
        flash(f"Blend failed: {e}", "danger")
        return redirect(next_url or url_for("inventory_adjust_page"))

    save_products(products)

    blend_display_name = result.get("blend_name") or (result.get("blend_product") or {}).get("name") or "Blend"
    msg = (
        f"Blended {result['total_gal']:.4f} GAL of '{blend_display_name}' "
        + (f"@ ${result['cost_per_gal']:.4f}/GAL " if can_see_costs() else "")
        + f"at {location_name}."
    )
    if result.get("packaged_gal"):
        pkg_label = ", ".join(result.get("package_summary") or [])
        msg += (
            f" Packaged {result['packaged_gal']:.4f} GAL ({pkg_label}); "
            f"Unpackaged remaining: {result.get('unpackaged_gal', 0):.4f} GAL."
        )
    flash(msg, "success")

    return redirect(next_url or url_for("inventory_adjust_page"))



# -------------------------
# Packages routes
# -------------------------

VALID_PACKAGE_UNITS = ("gal", "lb", "unit")

def _validate_package_unit(unit_raw):
    u = normalize_unit((unit_raw or "").strip().lower())
    if u not in VALID_PACKAGE_UNITS:
        raise ValueError("Unit must be GAL, LB, or UNIT.")
    return u


@app.route("/packages", methods=["GET"])
def packages_page():
    return render_template("packages.html", form={}, app_title=APP_TITLE)


@app.route("/packages/add", methods=["POST"])
def packages_add():
    errors = []
    name       = (request.form.get("name")     or "").strip()
    volume_raw = (request.form.get("volume")   or "").strip()
    unit_raw   = (request.form.get("unit")     or "gal").strip()
    notes      = (request.form.get("notes")    or "").strip() or None
    cost_raw   = (request.form.get("cost")     or "").strip()
    supplier   = (request.form.get("supplier") or "").strip() or None

    if not name:
        errors.append("Package name is required.")
    try:
        volume = float(volume_raw)
        if volume <= 0:
            errors.append("Volume must be > 0.")
    except (ValueError, TypeError):
        volume = None
        errors.append("Volume must be a valid number.")
    try:
        unit = _validate_package_unit(unit_raw)
    except ValueError as e:
        unit = "gal"
        errors.append(str(e))
    cost = None
    if cost_raw:
        try:
            cost = round(float(cost_raw), 4)
        except (ValueError, TypeError):
            errors.append("Cost must be a number if provided.")

    if errors:
        flash(" | ".join(errors), "danger")
        return render_template("packages.html", form=request.form.to_dict(), app_title=APP_TITLE)

    packages = load_packages()
    if any(pk.get("name", "").strip().lower() == name.lower() for pk in packages):
        flash(f"A package named '{name}' already exists.", "danger")
        return render_template("packages.html", form=request.form.to_dict(), app_title=APP_TITLE)

    packages.append({
        "id":         generate_next_package_id(packages),
        "name":       name,
        "volume":     round(float(volume), 4),
        "unit":       unit,
        "cost":       cost,
        "supplier":   supplier,
        "notes":      notes,
        "created_at": now_central_iso(),
        "updated_at": now_central_iso(),
    })
    save_packages(packages)
    flash(f"Package '{name}' created.", "success")
    return redirect(url_for("list_products"))


@app.route("/packages/<package_id>/edit", methods=["GET", "POST"])
def packages_edit(package_id):
    packages = load_packages()
    pkg = get_package_by_id(packages, package_id)
    if not pkg:
        flash("Package not found.", "danger")
        return redirect(url_for("list_products"))

    if request.method == "GET":
        return render_template("packages_edit.html", pkg=pkg, errors=[], form=None, app_title=APP_TITLE)

    errors = []
    name       = (request.form.get("name")     or "").strip()
    volume_raw = (request.form.get("volume")   or "").strip()
    unit_raw   = (request.form.get("unit")     or "gal").strip()
    notes      = (request.form.get("notes")    or "").strip() or None
    cost_raw   = (request.form.get("cost")     or "").strip()
    supplier   = (request.form.get("supplier") or "").strip() or None

    if not name:
        errors.append("Package name is required.")
    try:
        volume = float(volume_raw)
        if volume <= 0:
            errors.append("Volume must be > 0.")
    except (ValueError, TypeError):
        volume = None
        errors.append("Volume must be a valid number.")
    try:
        unit = _validate_package_unit(unit_raw)
    except ValueError as e:
        unit = pkg.get("unit", "gal")
        errors.append(str(e))
    cost = None
    if cost_raw:
        try:
            cost = round(float(cost_raw), 4)
        except (ValueError, TypeError):
            errors.append("Cost must be a number if provided.")
    if name and any(
        pk.get("name", "").strip().lower() == name.lower() and str(pk.get("id")) != package_id
        for pk in packages
    ):
        errors.append(f"Another package named '{name}' already exists.")

    if errors:
        return render_template("packages_edit.html", pkg=pkg, errors=errors,
                               form=request.form.to_dict(), app_title=APP_TITLE)

    if not can_see_costs():
        cost = pkg.get("cost")   # hidden field: keep the current package cost
    pkg.update({
        "name": name, "volume": round(float(volume), 4), "unit": unit,
        "cost": cost, "supplier": supplier, "notes": notes,
        "updated_at": now_central_iso(),
    })
    save_packages(packages)
    flash(f"Package '{name}' updated.", "success")
    return redirect(url_for("list_products"))


@app.route("/packages/<package_id>/delete", methods=["POST"])
def packages_delete(package_id):
    packages = load_packages()
    pkg = get_package_by_id(packages, package_id)
    if not pkg:
        flash("Package not found.", "danger")
        return redirect(url_for("list_products"))
    name = pkg.get("name", package_id)
    save_packages([pk for pk in packages if str(pk.get("id")) != package_id])
    flash(f"Package '{name}' deleted.", "success")
    return redirect(url_for("list_products"))


@app.route("/api/packages", methods=["GET"])
def api_packages_list():
    from flask import jsonify
    return jsonify([{
        "id": pk.get("id"), "name": pk.get("name"),
        "volume": pk.get("volume"), "unit": (pk.get("unit") or "unit").upper(),
        "cost": pk.get("cost"), "supplier": pk.get("supplier"),
    } for pk in load_packages()])


@app.route("/api/package_inventory/<product_id>", methods=["GET"])
def api_package_inventory(product_id):
    from flask import jsonify
    summary = get_package_inventory_summary(product_id)
    products = load_products()
    prod = next((p for p in products if str(p.get("id")) == str(product_id)), None)
    total_gal = 0.0
    packaged_gal = 0.0
    if prod:
        g, _ = compute_display_breakdown(prod)
        total_gal = g or 0.0
        packaged_gal = sum(
            package_volume_to_gallons(prod, t["total_volume"], t.get("unit"))
            for t in summary.values()
        )
    return jsonify({
        "product_id":         product_id,
        "total_gallons":      total_gal,
        "packaged":           list(summary.values()),
        "unpackaged_gallons": round(max(0.0, total_gal - packaged_gal), 4),
    })


@app.route("/api/location_inventory/<location_id>", methods=["GET"])
def api_location_inventory(location_id):
    from flask import jsonify
    return jsonify(compute_location_inventory(location_id))


# -------------------------
# Alerts routes
# -------------------------
@app.route("/alerts", methods=["GET"])
def alerts_page():
    products = load_products()
    rows, _ = compute_reorder_alerts_with_status()
    return render_template("reorder_alerts.html", products=products, alerts=rows, app_title=APP_TITLE)


@app.route("/alerts/add", methods=["POST"])
def alerts_add():
    pid = (request.form.get("product_id") or "").strip()
    unit = normalize_unit((request.form.get("unit") or "gal").lower())
    try:
        amount = float((request.form.get("amount") or "").strip())
    except ValueError:
        amount = 0.0

    prod = next((p for p in load_products() if p.get("id") == pid), None)
    if not prod:
        flash("Pick a product.", "danger")
        return redirect(url_for("alerts_page"))
    if amount <= 0:
        flash("The reorder point has to be more than 0.", "danger")
        return redirect(url_for("alerts_page"))
    try:
        convert_to_product_default_unit(prod, amount, unit)
    except Exception:
        flash(f"{prod.get('name')} can't be measured in {unit.upper()} (it needs a weight or package size set). "
              f"Use {normalize_unit(prod.get('default_unit')).upper()} instead.", "danger")
        return redirect(url_for("alerts_page"))

    # Keep the number in the unit it was typed in, so it displays the same way later
    alerts = load_alerts()
    existing = next((a for a in alerts if a.get("product_id") == pid), None)
    if existing:
        existing["threshold_value"] = amount
        existing["threshold_unit"] = unit.upper()
        flash(f"Updated the alert for {prod.get('name')}: reorder at {amount:g} {unit.upper()}.", "success")
    else:
        alerts.append({"product_id": pid, "threshold_value": amount, "threshold_unit": unit.upper()})
        flash(f"Added an alert for {prod.get('name')}: reorder at {amount:g} {unit.upper()}.", "success")
    save_alerts(alerts)
    return redirect(url_for("alerts_page"))


@app.route("/alerts/delete/<product_id>", methods=["POST"])
def alerts_delete(product_id):
    alerts = load_alerts()
    alerts = [a for a in alerts if a.get("product_id") != product_id]
    save_alerts(alerts)
    flash("Alert removed.", "success")
    return redirect(url_for("alerts_page"))


# -------------------------
# Receive inventory (FIFO version)
# -------------------------
@app.post("/products/<product_id>/receive")
def receive_inventory(product_id):
    products = load_products()
    idx, p = get_product_by_id(products, product_id)
    if not p:
        flash("Product not found.", "danger")
        return redirect(url_for("list_products"))

    try:
        recv_qty = float((request.form.get("receive_qty") or "0").strip())
        recv_cost = float((request.form.get("receive_unit_cost") or "0").strip())
    except ValueError:
        flash("Invalid quantity or cost.", "danger")
        return redirect(url_for("product_detail", product_id=product_id))

    if recv_qty <= 0 or recv_cost < 0:
        flash("Quantity must be > 0 and cost must be ≥ 0.", "danger")
        return redirect(url_for("product_detail", product_id=product_id))

    # Every receive must land at a real location (never "Unassigned")
    location_id = (request.form.get("location_id") or "").strip()
    loc = get_location_by_id(load_locations_for_user(), location_id) if location_id else None
    if not loc:
        flash("Please select a location.", "danger")
        return redirect(url_for("product_detail", product_id=product_id))
    effective_location = loc.get("name")

    migrate_products_to_layers(products)

    # receive_qty is assumed to be in product default unit (same as your UI currently)
    fifo_receive(p, recv_qty, recv_cost, location=effective_location)

    # keep the product's own location in sync (optional but nice)
    if effective_location:
        p["location"] = effective_location

    p["last_updated"] = central_time_now_str()

    save_products(products)

    flash(
        (f"Received {recv_qty} {p.get('default_unit','units')} at ${recv_cost}/unit. "
         f"New avg cost: ${p.get('unit_cost')}/unit. On-hand: {p.get('quantity')}.")
        if can_see_costs() else
        f"Received {recv_qty} {p.get('default_unit','units')}. On-hand: {p.get('quantity')}.",
        "success",
    )
    return redirect(url_for("product_detail", product_id=product_id))

@app.post("/api/formulas/compute")
def api_formula_compute():
    payload = request.get_json(silent=True) or {}
    mode = (payload.get("mode") or "percent").lower()
    target_unit = normalize_unit((payload.get("target_unit") or "gal").lower())
    try:
        target_qty = float(payload.get("target_qty") or 1.0)  # default 1 for percent calc
    except Exception:
        target_qty = 1.0

    components = payload.get("components") or []

    if mode != "percent":
        return {"ok": False, "errors": ["Only percent mode supported for live formula weight."]}, 400
    if target_unit not in ("gal", "lb"):
        return {"ok": False, "errors": ["target_unit must be 'gal' or 'lb'."]}, 400
    if target_qty <= 0:
        target_qty = 1.0

    products = load_products()
    by_id = index_products_by_id(products)

    # Build the same rows structure your blend uses
    rows = []
    total_pct = 0.0

    for c in components:
        pid = (c.get("product_id") or "").strip()
        if not pid:
            continue
        try:
            pct = float(c.get("percent") or 0.0)
        except Exception:
            pct = 0.0
        if pct <= 0:
            continue

        prod = by_id.get(pid)
        if not prod:
            continue

        total_pct += pct
        required_in_batch_unit = (pct / 100.0) * float(target_qty)

        # This gives us vol_gal for each component (key for lb/gal)
        q_prod, unit_str, vol_gal = convert_required_to_product_unit(prod, required_in_batch_unit, target_unit)

        rows.append({
            "product": prod,
            "vol_gal": float(vol_gal),
            "required_qty_in_product_unit": q_prod,
        })

    if not rows:
        return {"ok": True, "lb_per_gal": 0.0}, 200

    # If your products don’t have weight set, _need_weight will raise BlendError
    try:
        lb_per_gal = compute_weighted_lb_per_gal(rows)
    except BlendError as e:
        return {"ok": False, "errors": [str(e)]}, 400

    # Estimated cost to make 1 unit (same math as the Formula Catalog's Cost column)
    cost, cost_unit = formula_cost_per_unit(
        {"mode": "percent", "components": components, "defaults": {"target_unit": target_unit}}, by_id
    )
    return {
        "ok": True,
        "lb_per_gal": round(float(lb_per_gal), 6),
        "total_pct": round(total_pct, 6),
        "cost_per_unit": cost,
        "cost_unit": cost_unit,
    }, 200

@app.post("/formulas/<formula_id>/update_percent")
def formulas_update_percent(formula_id):
    formulas = load_formulas()
    f = get_formula_by_id(formulas, formula_id)
    if not f:
        flash("Formula not found.", "danger")
        return redirect(url_for("formulas_page"))

    name = (request.form.get("name") or "").strip()
    description = (request.form.get("description") or "").strip() or None

    target_unit = normalize_unit((request.form.get("target_unit") or "gal").lower())
    try:
        target_qty = float(request.form.get("target_qty") or 0.0)
    except Exception:
        target_qty = 0.0

    if not name:
        flash("Formula name is required.", "danger")
        return redirect(url_for("formulas_info_page", formula_id=formula_id))

    # parse arrays (same as create)
    pids = request.form.getlist("product_id[]")
    pcts = request.form.getlist("percent[]")

    components = []
    for pid, pct_raw in zip(pids, pcts):
        pid = (pid or "").strip()
        try:
            pct = float(pct_raw or 0.0)
        except Exception:
            pct = 0.0
        if pid and pct > 0:
            components.append({"product_id": pid, "percent": pct})

    if not components:
        flash("Add at least one product with a percent.", "danger")
        return redirect(url_for("formulas_info_page", formula_id=formula_id))

    total_pct = sum(float(c["percent"]) for c in components)
    if abs(total_pct - 100.0) > 0.001:
        flash(f"Percents must sum to 100%. Current total: {total_pct:.3f}%.", "danger")
        return redirect(url_for("formulas_info_page", formula_id=formula_id))

    # update record
    f["name"] = name
    f["description"] = description
    f["mode"] = "percent"
    f["defaults"] = {
        "target_qty": target_qty if target_qty > 0 else None,
        "target_unit": target_unit,
    }
    f["components"] = components
    f["updated_at"] = now_central_iso()

    save_formulas(formulas)

    flash("Formula updated.", "success")
    return redirect(url_for("formulas_info_page", formula_id=formula_id))
# -------------------------
# Dashboard + Inventory Overview
# -------------------------
# The ledger password is set by an admin on the Admin page and stored hashed in
# data/settings.json. LEDGER_PASSWORD in the environment still works as a fallback.
# There is no default: with neither set, the ledger stays locked.
LEDGER_PASSWORD = os.environ.get("LEDGER_PASSWORD", "")
SETTINGS_PATH = os.path.join(DATA_DIR, "settings.json")


def load_settings() -> dict:
    return load_json(SETTINGS_PATH, {})


def save_settings(settings: dict) -> None:
    save_json(SETTINGS_PATH, settings)


def ledger_password_is_set() -> bool:
    return bool(load_settings().get("ledger_password_hash") or LEDGER_PASSWORD)


def check_ledger_password(submitted: str) -> bool:
    stored = load_settings().get("ledger_password_hash")
    if stored:
        return check_password_hash(stored, submitted)
    if LEDGER_PASSWORD:
        return hmac.compare_digest(submitted.encode(), LEDGER_PASSWORD.encode())
    return False


@app.route("/ledger", methods=["GET", "POST"])
def event_ledger_page():
    """
    Hidden ledger viewer. Not linked anywhere in the nav — reached only by
    typing the URL directly or the Ctrl+L shortcut wired up in base.html.
    Gated by a server-side session flag; the password check happens here,
    not in client JS, so it never sits in the page source.
    """
    error = None

    if request.method == "POST":
        submitted = request.form.get("password", "")
        if not ledger_password_is_set():
            error = "The ledger password hasn't been set yet. An admin can set it on the Admin page."
        elif check_ledger_password(submitted):
            session["ledger_auth"] = True
            return redirect(url_for("event_ledger_page"))
        else:
            error = "Incorrect password."

    if not session.get("ledger_auth"):
        return render_template("ledger.html", authed=False, error=error)

    entries = load_ledger()
    chain_status = verify_ledger_chain(entries)   # verified on the real entries
    shown = list(reversed(entries))
    if not can_see_costs():
        shown = [dict(e, payload=strip_money(e.get("payload"))) for e in shown]

    return render_template(
        "ledger.html",
        authed=True,
        entries=shown,
        chain_status=chain_status,
    )


@app.route("/ledger/lock", methods=["POST"])
def event_ledger_lock():
    session.pop("ledger_auth", None)
    return redirect(url_for("event_ledger_page"))


@app.route("/dashboard")
def dashboard():
    """The Dashboard was replaced by Transaction History; old links land there."""
    return redirect(url_for("transactions_page"))


@app.route("/inventory-overview")
def inventory_overview():
    products = load_products()
    locations = load_locations_for_user()   # ✅ ADD THIS

    derived = []
    for p in products:
        p["default_unit"] = normalize_unit(p.get("default_unit"))
        gallons, pounds = compute_display_breakdown(p)
        inv_val = compute_item_value(p)
        derived.append({"raw": p, "gallons": gallons, "pounds": pounds, "inventory_value": inv_val})

    derived_sorted = sorted(derived, key=lambda it: float(it["raw"].get("quantity") or 0), reverse=True)
    top_items = derived_sorted[:8]

    kpis = compute_inventory_value()

    rows, _ = compute_reorder_alerts_with_status()
    alerts_triggered = sum(1 for r in rows if (r.get("ratio") is not None) and (r["ratio"] < 1.0))
    alerts_total = len(rows)
    alerts_by_pid = {r["product_id"]: r for r in rows if r.get("product_id")}

    return render_template(
        "inventory_overview.html",
        kpis=kpis,
        items=top_items,              # your “top items” cards/table
        products=products,            # ✅ ADD THIS (for Quick Adjust product dropdown)
        locations=locations,          # ✅ ADD THIS (for Quick Adjust location dropdown)
        product_count=len(products),
        alerts_triggered=alerts_triggered,
        alerts_total=alerts_total,
        alerts_by_pid=alerts_by_pid,
    )

@app.route("/locations")
def locations_page():
    locations = compute_inventory_by_location()
    allowed = allowed_location_ids(current_user())
    if allowed is not None:
        locations = [l for l in locations if str(l.get("location_id")) in allowed]
    return render_template("locations.html", app_title="Locations", locations=locations)


@app.route("/locations/<path:location_name>")
def location_detail_page(location_name):
    products = load_products()
    locations = load_locations()

    # Find address + id (optional)
    loc_rec = next(
        (l for l in locations if (l.get("name") or "").lower() == location_name.lower()),
        None
    )
    location_address = loc_rec.get("address") if loc_rec else None
    location_id = loc_rec.get("id") if loc_rec else None

    # -------------------------
    # Tanks (additive)
    # -------------------------
    tank_cards = []
    if location_id:
        tanks = get_tanks_for_location(load_tanks(), location_id)
        ledger = load_tank_ledger()

        for t in tanks:
            tid = t.get("id")
            cap = _safe_float(t.get("capacity_gal"), 0.0)
            fill = get_tank_fill_gal(ledger, tid)
            pct, label = tank_status(fill, cap)

            assigned_pid = t.get("assigned_product_id") or None
            assigned_name = product_name_by_id(products, assigned_pid) if assigned_pid else None

            tank_cards.append({
                "id": tid,
                "name": t.get("name") or tid,
                "capacity_gal": cap,
                "fill_gal": fill,
                "pct_full": pct,
                "status": label,  # empty/near_empty/ok/near_full/full
                "assigned_product_id": assigned_pid,
                "assigned_product_name": assigned_name,
            })

        tank_cards.sort(key=lambda x: str(x["name"]).lower())

    # -------------------------
    # Existing: products at location
    # -------------------------
    items = []
    total_value = total_gallons = total_pounds = 0.0
    sku_ids = set()

    # ---- Package columns (scoped to THIS location only) ----
    all_packages = load_packages()
    pkg_summaries = {}

    for p in products:
        _ensure_layers(p)
        default_unit = normalize_unit(p.get("default_unit"))
        weight = p.get("weight")

        qty_at_loc = 0.0
        value_at_loc = 0.0

        for layer in p.get("layers", []):
            if (layer.get("location") or "").strip().lower() == location_name.lower():
                q = float(layer.get("qty") or 0)
                c = float(layer.get("unit_cost") or 0)
                qty_at_loc += q
                value_at_loc += q * c

        if qty_at_loc > 0:
            sku_ids.add(p.get("id"))

            tmp = {
                "default_unit": default_unit,
                "quantity": qty_at_loc,
                "weight": weight,
            }
            gal, lb = compute_display_breakdown(tmp)

            if gal:
                total_gallons += gal
            if lb:
                total_pounds += lb

            total_value += value_at_loc

            items.append({
                "id": p.get("id"),
                "name": p.get("name"),
                "qty": qty_at_loc,
                "unit": default_unit,
                "unit_cost": p.get("unit_cost"),
                "value": value_at_loc,
                "gallons": gal,
                "pounds": lb,
                "last_updated": p.get("last_updated"),
            })

            if location_id:
                pid = str(p.get("id"))
                pkg_summary = get_package_inventory_summary_for_location(pid, location_id)
                total_packaged_gal = sum(
                    package_volume_to_gallons(p, t["total_volume"], t.get("unit"))
                    for t in pkg_summary.values()
                )
                pkg_summaries[pid] = {
                    "by_package": pkg_summary,
                    "unpackaged_gal": round(max(0.0, (gal or 0.0) - total_packaged_gal), 4),
                }

    kpis = {
        "total_value": round(total_value, 2),
        "total_gallons": round(total_gallons, 2),
        "total_pounds": round(total_pounds, 2),
        "sku_count": len(sku_ids),
        "total_unpackaged_gal": round(
            sum((v.get("unpackaged_gal") or 0.0) for v in pkg_summaries.values()), 2
        ),
    }

    items.sort(key=lambda x: (x.get("name") or "").lower())

    return render_template(
        "location_detail.html",
        app_title=location_name,
        location_name=location_name,
        location_address=location_address,
        location_id=location_id,   # ✅ ADD
        tanks=tank_cards,          # ✅ ADD
        kpis=kpis,
        items=items,
        all_packages=all_packages,
        pkg_summaries=pkg_summaries,
        recent_layers=None,
    )
@app.route("/locations/id/<location_id>")
def location_detail_by_id(location_id):
    products = load_products()
    locations = load_locations()

    loc = next((l for l in locations if str(l.get("id")) == str(location_id)), None)
    if not loc:
        flash("Location not found.", "danger")
        return redirect(url_for("locations_page"))

    location_name = loc.get("name") or "Location"
    location_address = loc.get("address")

    # ---- Tanks data (additive) ----
    tanks = get_tanks_for_location(load_tanks(), location_id)
    ledger = load_tank_ledger()

    # Build tank view models
    tank_cards = []
    for t in tanks:
        tid = t.get("id")
        cap = _safe_float(t.get("capacity_gal"), 0.0)
        fill = get_tank_fill_gal(ledger, tid)
        pct, label = tank_status(fill, cap)

        assigned_pid = t.get("assigned_product_id") or None
        assigned_name = product_name_by_id(products, assigned_pid) if assigned_pid else None

        tank_cards.append({
            "id": tid,
            "name": t.get("name") or tid,
            "capacity_gal": cap,
            "fill_gal": fill,
            "pct_full": pct,
            "status": label,
            "assigned_product_id": assigned_pid,
            "assigned_product_name": assigned_name,
        })
    tank_cards.sort(key=lambda x: str(x["name"]).lower())

    # ---- Existing product rollup by location NAME (keeps your system working) ----
    items = []
    total_value = total_gallons = total_pounds = 0.0
    sku_ids = set()

    # ---- Package columns (scoped to THIS location only) ----
    all_packages = load_packages()
    pkg_summaries = {}

    for p in products:
        _ensure_layers(p)
        default_unit = normalize_unit(p.get("default_unit"))
        weight = p.get("weight")

        qty_at_loc = 0.0
        value_at_loc = 0.0

        for layer in p.get("layers", []):
            if (layer.get("location") or "").strip().lower() == location_name.lower():
                q = float(layer.get("qty") or 0)
                c = float(layer.get("unit_cost") or 0)
                qty_at_loc += q
                value_at_loc += q * c

        if qty_at_loc > 0:
            sku_ids.add(p.get("id"))

            tmp = {"default_unit": default_unit, "quantity": qty_at_loc, "weight": weight}
            gal, lb = compute_display_breakdown(tmp)
            if gal: total_gallons += gal
            if lb:  total_pounds += lb

            total_value += value_at_loc

            items.append({
                "id": p.get("id"),
                "name": p.get("name"),
                "qty": qty_at_loc,
                "unit": default_unit,
                "unit_cost": p.get("unit_cost"),
                "value": value_at_loc,
                "gallons": gal,
                "pounds": lb,
                "last_updated": p.get("last_updated"),
            })

            pid = str(p.get("id"))
            pkg_summary = get_package_inventory_summary_for_location(pid, location_id)
            total_packaged_gal = sum(
                package_volume_to_gallons(p, t["total_volume"], t.get("unit"))
                for t in pkg_summary.values()
            )
            pkg_summaries[pid] = {
                "by_package": pkg_summary,
                "unpackaged_gal": round(max(0.0, (gal or 0.0) - total_packaged_gal), 4),
            }

    kpis = {
        "total_value": round(total_value, 2),
        "total_gallons": round(total_gallons, 2),
        "total_pounds": round(total_pounds, 2),
        "sku_count": len(sku_ids),
        "total_unpackaged_gal": round(
            sum((v.get("unpackaged_gal") or 0.0) for v in pkg_summaries.values()), 2
        ),
    }
    items.sort(key=lambda x: (x.get("name") or "").lower())

    return render_template(
        "location_detail.html",
        app_title=location_name,
        location_id=loc.get("id"),     # ✅ required by Tanks section
        location_name=location_name,
        location_address=location_address,
        kpis=kpis,
        items=items,
        all_packages=all_packages,
        pkg_summaries=pkg_summaries,
        tanks=tank_cards,              # ✅ required by Tanks section
        recent_layers=None,
    )

@app.route("/locations/id/<location_id>/edit", methods=["GET", "POST"])
def edit_location(location_id):
    locations = load_locations_safe()
    loc = get_location_by_id(locations, location_id)

    if not loc:
        flash("Location not found.", "danger")
        return redirect(url_for("locations_page"))

    tanks = load_tanks()
    ledger = load_tank_ledger()

    # only tanks for this location
    loc_tanks = [t for t in tanks if str(t.get("location_id")) == str(location_id)]
    loc_tanks.sort(key=lambda x: str(x.get("name") or "").lower())

    if request.method == "GET":
        return render_template(
            "edit_location.html",
            app_title="Edit Location",
            location=loc,
            tanks=loc_tanks,
            errors=[],
            form={}
        )

    # ---- POST ----
    errors = []

    name = _safe_str(request.form.get("name"))
    address = _safe_str(request.form.get("address"))

    if not name:
        errors.append("Location name is required.")

    # prevent duplicate names (excluding this same location)
    for other in locations:
        if str(other.get("id")) != str(location_id):
            if (other.get("name") or "").strip().lower() == name.lower():
                errors.append("A location with that name already exists.")
                break

    # ---------
    # Update tanks (existing)
    # ---------
    tank_ids   = request.form.getlist("tank_id[]")
    tank_names = request.form.getlist("tank_name[]")
    tank_caps  = request.form.getlist("tank_capacity_gal[]")
    tank_notes = request.form.getlist("tank_notes[]")

    tank_by_id = {str(t.get("id")): t for t in tanks}

    for tid, nm, cap_raw, note in zip(tank_ids, tank_names, tank_caps, tank_notes):
        tid = str(tid or "").strip()
        if not tid:
            continue

        t = tank_by_id.get(tid)
        if not t:
            continue

        # safety: only allow edits on tanks in this location
        if str(t.get("location_id")) != str(location_id):
            continue

        nm = (nm or "").strip()
        note = (note or "").strip() or None
        cap_raw = (cap_raw or "").strip()

        if not nm:
            errors.append(f"Tank {tid}: name is required.")
            continue

        try:
            cap = float(cap_raw)
            if cap <= 0:
                errors.append(f"Tank {tid}: capacity must be > 0.")
                continue
        except Exception:
            errors.append(f"Tank {tid}: capacity must be a number.")
            continue

        # do not allow capacity below current fill
        fill = get_tank_fill_gal(ledger, tid)  # you already have this helper :contentReference[oaicite:4]{index=4}
        if cap + 1e-9 < float(fill):
            errors.append(f"Tank {tid}: capacity cannot be less than current fill ({fill:.2f} gal).")
            continue

        t["name"] = nm
        t["capacity_gal"] = float(cap)
        t["notes"] = note

    # ---------
    # Add new tanks (optional)
    # ---------
    new_names = request.form.getlist("new_tank_name[]")
    new_caps  = request.form.getlist("new_tank_capacity_gal[]")
    new_notes = request.form.getlist("new_tank_notes[]")

    # use a working list so IDs never collide
    working_tanks = list(tanks)

    for nm, cap_raw, note in zip(new_names, new_caps, new_notes):
        nm = (nm or "").strip()
        cap_raw = (cap_raw or "").strip()
        note = (note or "").strip() or None

        if not nm:
            continue

        try:
            cap = float(cap_raw)
            if cap <= 0:
                errors.append(f"New tank '{nm}': capacity must be > 0.")
                continue
        except Exception:
            errors.append(f"New tank '{nm}': capacity must be a number.")
            continue

        new_tid = generate_next_tank_id(working_tanks)
        new_tank = {
            "id": new_tid,
            "location_id": str(location_id),
            "name": nm,
            "capacity_gal": float(cap),
            "assigned_product_id": None,
            "is_active": True,
            "notes": note,
            "created_at": now_central_iso(),
        }
        tanks.append(new_tank)
        working_tanks.append(new_tank)

    if errors:
        # re-render with latest tank list for this location
        loc_tanks = [t for t in tanks if str(t.get("location_id")) == str(location_id)]
        loc_tanks.sort(key=lambda x: str(x.get("name") or "").lower())

        return render_template(
            "edit_location.html",
            app_title="Edit Location",
            location=loc,
            tanks=loc_tanks,
            errors=errors,
            form=request.form.to_dict()
        )

    # Update location record (inventory untouched)
    loc["name"] = name
    loc["address"] = address
    loc["updated_at"] = now_central_iso()

    save_locations(locations)
    save_tanks(tanks)

    flash("Location updated.", "success")
    return redirect(url_for("location_detail_by_id", location_id=location_id))

@app.route("/spreadsheet")
def spreadsheet_page():
    return render_template("nstock_spreadsheet.html")

SPREADSHEET_PATH = os.path.join(DATA_DIR, "spreadsheet.json")  # old single-sheet file (migrated once)
SHEETS_INDEX_PATH = os.path.join(DATA_DIR, "sheets.json")
SHEETS_DIR = os.path.join(DATA_DIR, "sheets")
EMPTY_SHEET = {"cells": {}, "fmt": {}, "rows": 200, "cols": 52, "colWidths": {}, "rowHeights": {}}
MAX_SHEET_NAME = 40


def _sheet_path(sheet_id: str) -> str:
    # ids are hex from uuid4, so this can't escape the folder
    return os.path.join(SHEETS_DIR, f"{sheet_id}.json")


def load_sheets_index() -> list:
    """List of sheets (metadata only). Creates 'Sheet 1' from the old spreadsheet on first run."""
    sheets = load_json(SHEETS_INDEX_PATH, None)
    if sheets is None:
        os.makedirs(SHEETS_DIR, exist_ok=True)
        first = {
            "id": uuid.uuid4().hex,
            "name": "Sheet 1",
            "created_at": now_central_iso(),
            "created_by": None,
            "locked": False,
            "allowed_users": [],
        }
        old = load_json(SPREADSHEET_PATH, None) if os.path.exists(SPREADSHEET_PATH) else None
        save_json(_sheet_path(first["id"]), old or dict(EMPTY_SHEET))
        sheets = [first]
        save_json(SHEETS_INDEX_PATH, sheets)
    return sheets


def save_sheets_index(sheets: list) -> None:
    save_json(SHEETS_INDEX_PATH, sheets)


def user_can_open_sheet(user, sheet: dict) -> bool:
    if not user:
        return False
    if user.get("role") == "admin":
        return True
    if not sheet.get("locked"):
        return True
    return user.get("id") in sheet.get("allowed_users", [])


def visible_sheets(user) -> list:
    return [sh for sh in load_sheets_index() if user_can_open_sheet(user, sh)]


def _find_sheet(sheet_id):
    return next((sh for sh in load_sheets_index() if sh["id"] == sheet_id), None)


def _clean_sheet_name(name: str):
    name = (name or "").strip()
    if not name:
        return None, "Sheet name can't be empty."
    if len(name) > MAX_SHEET_NAME:
        return None, f"Sheet name must be {MAX_SHEET_NAME} characters or less."
    return name, None


def _sheet_for_request(user):
    """The sheet named in ?sheet=, or the first one this user can open."""
    sheet_id = request.args.get("sheet")
    if sheet_id:
        sh = _find_sheet(sheet_id)
        if sh and user_can_open_sheet(user, sh):
            return sh, None
        return None, (jsonify({"error": "You don't have access to that sheet."}), 403)
    vis = visible_sheets(user)
    if not vis:
        return None, (jsonify({"error": "No sheets available."}), 404)
    return vis[0], None


@app.route("/api/sheets", methods=["GET"])
def api_sheets_list():
    user = current_user()
    return jsonify([
        {"id": sh["id"], "name": sh["name"], "locked": bool(sh.get("locked"))}
        for sh in visible_sheets(user)
    ])


@app.route("/api/sheets", methods=["POST"])
def api_sheets_create():
    user = current_user()
    body = request.get_json(silent=True) or {}
    sheets = load_sheets_index()
    name, err = _clean_sheet_name(body.get("name") or f"Sheet {len(sheets) + 1}")
    if err:
        return jsonify({"error": err}), 400
    if any(sh["name"].lower() == name.lower() for sh in sheets):
        return jsonify({"error": "A sheet with that name already exists."}), 400
    sheet = {
        "id": uuid.uuid4().hex,
        "name": name,
        "created_at": now_central_iso(),
        "created_by": user["id"],
        "locked": False,
        "allowed_users": [],
    }
    os.makedirs(SHEETS_DIR, exist_ok=True)
    save_json(_sheet_path(sheet["id"]), dict(EMPTY_SHEET))
    sheets.append(sheet)
    save_sheets_index(sheets)
    append_ledger_entry("sheet_created", {"sheet": name, "by": user["username"]})
    return jsonify({"id": sheet["id"], "name": sheet["name"], "locked": False})


@app.route("/api/sheets/<sheet_id>/rename", methods=["POST"])
def api_sheets_rename(sheet_id):
    user = current_user()
    sheets = load_sheets_index()
    sheet = next((sh for sh in sheets if sh["id"] == sheet_id), None)
    if not sheet or not user_can_open_sheet(user, sheet):
        return jsonify({"error": "Sheet not found."}), 404
    name, err = _clean_sheet_name((request.get_json(silent=True) or {}).get("name"))
    if err:
        return jsonify({"error": err}), 400
    if any(sh["name"].lower() == name.lower() and sh["id"] != sheet_id for sh in sheets):
        return jsonify({"error": "A sheet with that name already exists."}), 400
    old = sheet["name"]
    sheet["name"] = name
    save_sheets_index(sheets)
    append_ledger_entry("sheet_renamed", {"sheet": name, "was": old, "by": user["username"]})
    return jsonify({"id": sheet["id"], "name": name, "locked": bool(sheet.get("locked"))})


@app.route("/api/sheets/<sheet_id>/delete", methods=["POST"])
def api_sheets_delete(sheet_id):
    user = current_user()
    sheets = load_sheets_index()
    sheet = next((sh for sh in sheets if sh["id"] == sheet_id), None)
    if not sheet or not user_can_open_sheet(user, sheet):
        return jsonify({"error": "Sheet not found."}), 404
    # Only admins or whoever made the sheet can delete it.
    if user.get("role") != "admin" and sheet.get("created_by") != user["id"]:
        return jsonify({"error": "Only an admin or the person who made this sheet can delete it."}), 403
    if len(sheets) <= 1:
        return jsonify({"error": "You can't delete the last sheet."}), 400
    sheets = [sh for sh in sheets if sh["id"] != sheet_id]
    save_sheets_index(sheets)
    try:
        os.replace(_sheet_path(sheet_id), _sheet_path(sheet_id) + ".deleted")  # keep a recoverable copy
    except FileNotFoundError:
        pass
    append_ledger_entry("sheet_deleted", {"sheet": sheet["name"], "by": user["username"]})
    return jsonify({"success": True})


@app.route("/api/spreadsheet/save", methods=["POST"])
def spreadsheet_save():
    sheet, err = _sheet_for_request(current_user())
    if err:
        return err
    data = request.get_json(force=True)
    save_json(_sheet_path(sheet["id"]), {
        "cells":      data.get("cells", {}),
        "fmt":        data.get("fmt", {}),
        "rows":       data.get("rows", 200),
        "cols":       data.get("cols", 52),
        "colWidths":  data.get("colWidths", {}),
        "rowHeights": data.get("rowHeights", {}),
    })
    return jsonify({"success": True})


@app.route("/api/spreadsheet/load")
def spreadsheet_load():
    sheet, err = _sheet_for_request(current_user())
    if err:
        return err
    data = load_json(_sheet_path(sheet["id"]), dict(EMPTY_SHEET))
    data["sheet"] = {"id": sheet["id"], "name": sheet["name"], "locked": bool(sheet.get("locked"))}
    return jsonify(data)


@app.route("/admin/ledger-password", methods=["POST"])
@admin_required
def admin_ledger_password():
    me = current_user()
    pw = request.form.get("password", "")
    error = _validate_new_password(pw, request.form.get("confirm", ""))
    if not error and len(pw) < 12:
        error = "Ledger password must be at least 12 characters."
    if error:
        flash(error, "danger")
        return redirect(url_for("admin_page") + "#ledger")
    settings = load_settings()
    settings["ledger_password_hash"] = generate_password_hash(pw)
    settings["ledger_password_set_at"] = now_central_iso()
    settings["ledger_password_set_by"] = me["username"]
    save_settings(settings)
    session.pop("ledger_auth", None)
    append_ledger_entry("ledger_password_changed", {"by": me["username"]})
    flash("Ledger password updated.", "success")
    return redirect(url_for("admin_page") + "#ledger")


@app.route("/admin/sheets/<sheet_id>", methods=["POST"])
@admin_required
def admin_sheet_access(sheet_id):
    me = current_user()
    sheets = load_sheets_index()
    sheet = next((sh for sh in sheets if sh["id"] == sheet_id), None)
    if not sheet:
        flash("Sheet not found.", "danger")
        return redirect(url_for("admin_page") + "#sheets")
    valid_ids = {u["id"] for u in load_users()}
    sheet["locked"] = request.form.get("locked") == "1"
    sheet["allowed_users"] = [uid for uid in request.form.getlist("allowed_users") if uid in valid_ids]
    save_sheets_index(sheets)
    names = [u["username"] for u in load_users() if u["id"] in sheet["allowed_users"]]
    append_ledger_entry("sheet_access_changed", {
        "sheet": sheet["name"], "locked": sheet["locked"], "allowed_users": names, "by": me["username"],
    })
    flash(f"Access for “{sheet['name']}” saved.", "success")
    return redirect(url_for("admin_page") + "#sheets")


@app.route("/api/data-context")
def api_data_context():
    raw_products  = load_products()
    ledger        = load_tank_ledger()
    raw_tanks     = load_tanks()
    raw_locations = load_locations()

    loc_by_id  = {str(l.get("id")): l.get("name", "") for l in raw_locations}
    prod_by_id = {str(p.get("id")): p.get("name", "") for p in raw_products}

    # ── Products ──────────────────────────────────────────
    products_out = []
    for p in raw_products:
        qty       = float(p.get("quantity") or 0.0)
        unit_cost = float(p.get("unit_cost") or 0.0)
        layers    = p.get("layers") or []
        total_val = sum(float(l.get("qty", 0)) * float(l.get("unit_cost", 0)) for l in layers)
        total_qty = sum(float(l.get("qty", 0)) for l in layers)
        avg_cog   = round(total_val / total_qty, 4) if total_qty > 0 else unit_cost
        # Compute gal/lb quantities using the same logic as compute_display_breakdown
        default_unit = (p.get("default_unit") or "unit").lower()
        wpg = p.get("weight")
        try:
            wpg_val = float(wpg) if wpg not in (None, "") else None
        except Exception:
            wpg_val = None

        if default_unit == "gal":
            qty_gal = round(qty, 4)
            qty_lb  = round(qty * wpg_val, 4) if wpg_val else None
        elif default_unit == "lb":
            qty_lb  = round(qty, 4)
            qty_gal = round(qty / wpg_val, 4) if wpg_val and wpg_val != 0 else None
        else:
            qty_gal = None
            qty_lb  = None

        products_out.append({
            "id":            p.get("id"),
            "name":          p.get("name", ""),
            "sku":           p.get("sku", ""),
            "category":      p.get("category", ""),
            "description":   p.get("description", ""),
            "status":        p.get("status", "active"),
            "unit":          p.get("default_unit", "UNIT"),
            "onhand":        round(qty, 4),
            "qty_gal":       qty_gal,
            "qty_lb":        qty_lb,
            "weight":        wpg_val,
            "unit_cost":     round(unit_cost, 4),
            "avg_cog":       avg_cog,
            "inv_value":     round(qty * unit_cost, 2),
            "location":      p.get("location", ""),
            "reorder_point": float(p.get("reorder_point") or 0.0),
            "reorder_qty":   float(p.get("reorder_qty") or 0.0),
            "last_updated":  p.get("last_updated", ""),
        })

    # ── Tanks ─────────────────────────────────────────────
    tanks_out = []
    for t in raw_tanks:
        tank_id      = str(t.get("id"))
        capacity_gal = float(t.get("capacity_gal") or 0.0)
        fill_gal     = get_tank_fill_gal(ledger, tank_id)
        pct_full     = round(fill_gal / capacity_gal * 100, 1) if capacity_gal > 0 else 0.0
        assigned_pid = str(t.get("assigned_product_id") or "")
        loc_id       = str(t.get("location_id") or "")
        tanks_out.append({
            "id":           tank_id,
            "name":         t.get("name", ""),
            "location":     loc_by_id.get(loc_id, loc_id),
            "location_id":  loc_id,
            "product":      prod_by_id.get(assigned_pid, ""),
            "product_id":   assigned_pid,
            "capacity_gal": round(capacity_gal, 2),
            "level_gal":    round(fill_gal, 2),
            "pct_full":     pct_full,
            "pct_empty":    round(100.0 - pct_full, 1),
            "is_active":    t.get("is_active", True),
            "notes":        t.get("notes", ""),
        })

    # ── Locations ─────────────────────────────────────────
    locations_out = []
    for loc in raw_locations:
        loc_id      = str(loc.get("id"))
        total_value = 0.0
        total_prods = 0
        for p in raw_products:
            loc_qty = float((p.get("location_qty") or {}).get(loc_id, 0.0))
            if loc_qty > 0:
                total_prods += 1
                total_value += loc_qty * float(p.get("unit_cost") or 0.0)
        locations_out.append({
            "id":             loc_id,
            "name":           loc.get("name", ""),
            "address":        loc.get("address", ""),
            "total_value":    round(total_value, 2),
            "total_products": total_prods,
            "created_at":     loc.get("created_at", ""),
        })

    # ── Vendors ───────────────────────────────────────────
    VENDORS_PATH = os.path.join(DATA_DIR, "vendors.json")
    vendors_out = []
    for v in load_json(VENDORS_PATH, []):
        vendors_out.append({
            "id":      v.get("id"),
            "name":    v.get("name", ""),
            "contact": v.get("contact", ""),
            "phone":   v.get("phone", ""),
            "email":   v.get("email", ""),
            "address": v.get("address", ""),
        })

    return jsonify({
        "products":  products_out,
        "tanks":     tanks_out,
        "locations": locations_out,
        "vendors":   vendors_out,
    })


# =========================================================
# Report Center
# =========================================================
#
# Every report below can be filtered by Location ("ALL" = entire
# company, or a specific location name) and, where it applies, by a
# Start Date / End Date range. That range filters which FIFO layers
# (receiving history) are counted — it is NOT a reconstruction of a
# past point-in-time snapshot, since not every inventory movement
# (adjustments, staging releases, etc.) is written to a full history
# log that would make that reconstruction reliable. Leaving both
# dates blank includes a product's entire receiving history, which
# is equivalent to "current on-hand."
# -------------------------

def _parse_report_date(s):
    """Parse a 'YYYY-MM-DD' input date string into a date object, else None."""
    if not s:
        return None
    try:
        return datetime.strptime(s.strip(), "%Y-%m-%d").date()
    except Exception:
        return None


def _parse_layer_date(dt_str):
    """Best-effort parse of a stored layer/ledger datetime string into a date object."""
    if not dt_str:
        return None
    s = str(dt_str).strip()
    try:
        return datetime.fromisoformat(s).date()
    except Exception:
        pass
    for fmt in ("%Y-%m-%d %H:%M", "%Y-%m-%d"):
        try:
            return datetime.strptime(s, fmt).date()
        except Exception:
            continue
    return None


def _layer_in_range(layer, start_d, end_d):
    if not start_d and not end_d:
        return True
    d = _parse_layer_date(layer.get("datetime"))
    if d is None:
        # Can't verify the date on this layer — include it rather than
        # silently dropping real inventory from the report.
        return True
    if start_d and d < start_d:
        return False
    if end_d and d > end_d:
        return False
    return True


def _layer_matches_location(layer, location_filter):
    if not location_filter or location_filter.strip().upper() == "ALL":
        return True
    return (layer.get("location") or "").strip().lower() == location_filter.strip().lower()


def _report_location_choices():
    locs = load_locations()
    names = sorted({(l.get("name") or "").strip() for l in locs if (l.get("name") or "").strip()})
    return names


def _gather_layer_rows(location_filter=None, start_date=None, end_date=None):
    """One row per (product, matching layer) after location + date filters."""
    products = load_products()
    rows = []
    for p in products:
        _ensure_layers(p)
        default_unit = normalize_unit(p.get("default_unit"))
        for layer in p.get("layers", []):
            if not _layer_matches_location(layer, location_filter):
                continue
            if not _layer_in_range(layer, start_date, end_date):
                continue
            qty = float(layer.get("qty") or 0.0)
            cost = float(layer.get("unit_cost") or 0.0)
            rows.append({
                "product_id": p.get("id"),
                "product_name": p.get("name") or "(unnamed)",
                "location": (layer.get("location") or "UNASSIGNED").strip() or "UNASSIGNED",
                "qty": qty,
                "unit_cost": cost,
                "value": qty * cost,
                "datetime": layer.get("datetime"),
                "default_unit": default_unit,
                "weight": p.get("weight"),
            })
    return rows


def build_inventory_value_report(location_filter, start_date, end_date):
    rows = _gather_layer_rows(location_filter, start_date, end_date)

    by_location = {}
    by_product = {}
    for r in rows:
        loc = r["location"]
        entry = by_location.setdefault(loc, {"location": loc, "qty_gal": 0.0, "qty_lb": 0.0, "value": 0.0, "sku_ids": set()})
        entry["value"] += r["value"]
        entry["sku_ids"].add(r["product_id"])
        tmp = {"default_unit": r["default_unit"], "quantity": r["qty"], "weight": r["weight"]}
        gal, lb = compute_display_breakdown(tmp)
        if gal is not None:
            entry["qty_gal"] += gal
        if lb is not None:
            entry["qty_lb"] += lb

        key = (r["product_id"], loc)
        bp = by_product.setdefault(key, {
            "product_id": r["product_id"], "product_name": r["product_name"], "location": loc,
            "qty": 0.0, "value": 0.0, "unit": r["default_unit"],
        })
        bp["qty"] += r["qty"]
        bp["value"] += r["value"]

    locations_out = []
    for loc, d in by_location.items():
        locations_out.append({
            "location": loc,
            "qty_gal": round(d["qty_gal"], 2),
            "qty_lb": round(d["qty_lb"], 2),
            "value": round(d["value"], 2),
            "sku_count": len(d["sku_ids"]),
        })
    locations_out.sort(key=lambda x: x["location"].lower())

    products_out = list(by_product.values())
    for p in products_out:
        p["qty"] = round(p["qty"], 2)
        p["value"] = round(p["value"], 2)
        p["avg_cost"] = round(p["value"] / p["qty"], 4) if p["qty"] else 0.0
    products_out.sort(key=lambda x: (x["location"].lower(), (x["product_name"] or "").lower()))

    grand_total = round(sum(d["value"] for d in locations_out), 2)

    return {"locations": locations_out, "products": products_out, "grand_total": grand_total}


def build_avg_cost_report(location_filter, start_date, end_date):
    rows = _gather_layer_rows(location_filter, start_date, end_date)

    by_product = {}
    for r in rows:
        pid = r["product_id"]
        bp = by_product.setdefault(pid, {
            "product_id": pid, "product_name": r["product_name"], "unit": r["default_unit"],
            "total_qty": 0.0, "total_value": 0.0,
        })
        bp["total_qty"] += r["qty"]
        bp["total_value"] += r["value"]

    out = []
    for pid, d in by_product.items():
        avg_cost = (d["total_value"] / d["total_qty"]) if d["total_qty"] else 0.0
        out.append({
            "product_id": pid,
            "product_name": d["product_name"],
            "unit": d["unit"],
            "total_qty": round(d["total_qty"], 2),
            "avg_unit_cost": round(avg_cost, 4),
            "total_value": round(d["total_value"], 2),
        })
    out.sort(key=lambda x: (x["product_name"] or "").lower())

    company_total_qty = sum(x["total_qty"] for x in out)
    company_total_value = sum(x["total_value"] for x in out)
    company_avg = (company_total_value / company_total_qty) if company_total_qty else 0.0

    return {"products": out, "company_avg_cost": round(company_avg, 4)}


def compute_formula_current_cost(formula, products_by_id, batch_gal=100.0):
    """Current cost/gal for a percent-mode formula, priced off today's component unit costs."""
    rows = []
    missing = []
    for c in (formula.get("components") or []):
        pid = str(c.get("product_id"))
        product = products_by_id.get(pid)
        pct = float(c.get("percent") or 0.0)
        if not product:
            missing.append(pid)
            continue
        vol_gal = batch_gal * pct / 100.0
        try:
            req_qty, unit, _ref_gal = convert_required_to_product_unit(product, vol_gal, "gal")
        except Exception:
            req_qty, unit = None, None
        rows.append({
            "product": product, "vol_gal": vol_gal,
            "required_qty_in_product_unit": req_qty, "unit": unit, "percent": pct,
        })

    total_gal = sum(r["vol_gal"] for r in rows)
    cost_per_gal = compute_weighted_unit_cost_per_gal(rows) if rows else 0.0
    total_cost = cost_per_gal * total_gal

    return {
        "rows": rows,
        "cost_per_gal": round(cost_per_gal, 4),
        "batch_cost": round(total_cost, 2),
        "batch_gal": round(total_gal, 2),
        "missing_products": missing,
    }


def build_blend_cost_report(formula_ids=None):
    formulas = load_formulas()
    if formula_ids:
        formulas = [f for f in formulas if f.get("id") in formula_ids]
    products = load_products()
    products_by_id = {str(p.get("id")): p for p in products}

    out = []
    for f in formulas:
        result = compute_formula_current_cost(f, products_by_id)
        out.append({
            "formula_id": f.get("id"),
            "formula_name": f.get("name") or "(unnamed formula)",
            "cost_per_gal": result["cost_per_gal"],
            "batch_cost": result["batch_cost"],
            "batch_gal": result["batch_gal"],
            "missing_products": result["missing_products"],
            "components": [
                {
                    "product_name": r["product"].get("name"),
                    "percent": r["percent"],
                    "unit_cost": float(r["product"].get("unit_cost") or 0.0),
                }
                for r in result["rows"]
            ],
        })
    out.sort(key=lambda x: (x["formula_name"] or "").lower())
    return out


def build_cycle_count_sheet(location_filter, count):
    products = load_products()

    filtered = bool(location_filter and location_filter.strip().upper() != "ALL")
    loc_key = location_filter.strip().lower() if filtered else None
    pool = []  # (product, location name)
    for p in products:
        _ensure_layers(p)
        locs = {}
        for l in p.get("layers", []):
            name = (l.get("location") or "").strip()
            if name and float(l.get("qty") or 0) > 0:
                locs.setdefault(name.lower(), name)
        base = (p.get("location") or "").strip()
        if base:
            locs.setdefault(base.lower(), base)
        if filtered:
            if loc_key in locs:
                pool.append((p, locs[loc_key]))
        elif locs:
            pool.extend((p, name) for name in locs.values())
        else:
            pool.append((p, ""))

    try:
        count = int(count)
    except Exception:
        count = 10
    count = max(1, count)
    count = min(count, len(pool)) if pool else 0

    chosen = random.sample(pool, count) if pool else []
    rows = []
    for p, loc_name in chosen:
        rows.append({
            "product_id": p.get("id"),
            "product_name": p.get("name") or "(unnamed)",
            "location": loc_name,
            "default_unit": normalize_unit(p.get("default_unit")),
        })
    rows.sort(key=lambda x: ((x["product_name"] or "").lower(), (x["location"] or "").lower()))
    return rows


# -------------------------
# Report Center — PDF builders (reportlab)
# -------------------------

def _pdf_header(elements, styles, title, subtitle_lines):
    from reportlab.platypus import Paragraph, Spacer
    elements.append(Paragraph(title, styles["ReportTitle"]))
    for line in subtitle_lines:
        elements.append(Paragraph(line, styles["ReportSubtitle"]))
    elements.append(Spacer(1, 14))


def _get_report_styles():
    from reportlab.lib.styles import getSampleStyleSheet, ParagraphStyle
    from reportlab.lib import colors
    styles = getSampleStyleSheet()
    styles.add(ParagraphStyle(name="ReportTitle", fontSize=18, leading=22, spaceAfter=2, fontName="Helvetica-Bold"))
    styles.add(ParagraphStyle(name="ReportSubtitle", fontSize=10, leading=13, textColor=colors.HexColor("#555555")))
    styles.add(ParagraphStyle(name="SectionHeading", fontSize=13, leading=16, spaceBefore=14, spaceAfter=6, fontName="Helvetica-Bold"))
    return styles


def _make_table(data, col_widths, header_bg="#2c3e50", align_right_cols=None):
    from reportlab.platypus import Table, TableStyle
    from reportlab.lib import colors

    align_right_cols = align_right_cols or []
    t = Table(data, colWidths=col_widths, repeatRows=1)
    style = [
        ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor(header_bg)),
        ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
        ("FONTNAME", (0, 0), (-1, 0), "Helvetica-Bold"),
        ("FONTSIZE", (0, 0), (-1, -1), 9),
        ("ROWBACKGROUNDS", (0, 1), (-1, -1), [colors.white, colors.HexColor("#f4f6f8")]),
        ("GRID", (0, 0), (-1, -1), 0.5, colors.HexColor("#d9dee3")),
        ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
        ("TOPPADDING", (0, 0), (-1, -1), 5),
        ("BOTTOMPADDING", (0, 0), (-1, -1), 5),
        ("LEFTPADDING", (0, 0), (-1, -1), 6),
        ("RIGHTPADDING", (0, 0), (-1, -1), 6),
    ]
    for c in align_right_cols:
        style.append(("ALIGN", (c, 0), (c, -1), "RIGHT"))
    t.setStyle(TableStyle(style))
    return t


def _report_scope_line(location, start_date_str, end_date_str):
    loc_txt = "Entire Company (all locations)" if (not location or location.strip().upper() == "ALL") else f"Location: {location}"
    if start_date_str or end_date_str:
        range_txt = f"Date range: {start_date_str or 'earliest'} to {end_date_str or 'today'}"
    else:
        range_txt = "Date range: all history (current on-hand)"
    return f"{loc_txt} &nbsp;&nbsp;|&nbsp;&nbsp; {range_txt}"


def _build_pdf_buffer(build_fn):
    from reportlab.lib.pagesizes import letter
    from reportlab.platypus import SimpleDocTemplate
    buf = io.BytesIO()
    doc = SimpleDocTemplate(
        buf, pagesize=letter,
        leftMargin=40, rightMargin=40, topMargin=40, bottomMargin=36,
        title="NStock Report",
    )
    elements = []
    build_fn(elements)
    doc.build(elements)
    buf.seek(0)
    return buf


def pdf_inventory_value(data, location, start_date_str, end_date_str):
    from reportlab.platypus import Paragraph, Spacer

    def build(elements):
        styles = _get_report_styles()
        _pdf_header(elements, styles, "Total Inventory Value Report", [
            _report_scope_line(location, start_date_str, end_date_str),
            f"Generated {now_central_str()}",
        ])

        rows = [["Location", "Gallons", "Pounds", "SKUs", "Value"]]
        for l in data["locations"]:
            rows.append([
                l["location"],
                f'{l["qty_gal"]:,.2f}' if l["qty_gal"] else "—",
                f'{l["qty_lb"]:,.2f}' if l["qty_lb"] else "—",
                str(l["sku_count"]),
                f'${l["value"]:,.2f}',
            ])
        rows.append(["TOTAL", "", "", "", f'${data["grand_total"]:,.2f}'])
        elements.append(_make_table(rows, [170, 90, 90, 60, 90], align_right_cols=[1, 2, 3, 4]))

        elements.append(Paragraph("By Product", styles["SectionHeading"]))
        prow = [["Product", "Location", "Qty", "Avg Cost", "Value"]]
        for p in data["products"]:
            prow.append([
                p["product_name"], p["location"],
                f'{p["qty"]:,.2f} {p["unit"]}', f'${p["avg_cost"]:,.4f}', f'${p["value"]:,.2f}',
            ])
        elements.append(_make_table(prow, [150, 100, 110, 80, 80], align_right_cols=[2, 3, 4]))
        elements.append(Spacer(1, 10))

    return _build_pdf_buffer(build)


def pdf_avg_cost(data, location, start_date_str, end_date_str):
    from reportlab.platypus import Paragraph

    def build(elements):
        styles = _get_report_styles()
        _pdf_header(elements, styles, "Average Cost of Goods Report", [
            _report_scope_line(location, start_date_str, end_date_str),
            f"Generated {now_central_str()}",
            f'Company-wide average unit cost: ${data["company_avg_cost"]:,.4f}',
        ])

        rows = [["Product", "Total Qty", "Avg Unit Cost", "Total Value"]]
        for p in data["products"]:
            rows.append([
                p["product_name"], f'{p["total_qty"]:,.2f} {p["unit"]}',
                f'${p["avg_unit_cost"]:,.4f}', f'${p["total_value"]:,.2f}',
            ])
        elements.append(_make_table(rows, [200, 130, 110, 110], align_right_cols=[1, 2, 3]))

    return _build_pdf_buffer(build)


def pdf_inventory_listing(data, location, start_date_str, end_date_str, show_costs=True):
    from reportlab.platypus import Paragraph

    def build(elements):
        styles = _get_report_styles()
        _pdf_header(elements, styles, "Total Inventory Report", [
            _report_scope_line(location, start_date_str, end_date_str),
            f"Generated {now_central_str()}",
        ])
        if show_costs:
            rows = [["Product", "Location", "On-Hand Qty", "Value"]]
            for p in data["products"]:
                rows.append([p["product_name"], p["location"], f'{p["qty"]:,.2f} {p["unit"]}', f'${p["value"]:,.2f}'])
            rows.append(["", "", "TOTAL", f'${data["grand_total"]:,.2f}'])
            elements.append(_make_table(rows, [220, 130, 110, 90], align_right_cols=[2, 3]))
        else:
            rows = [["Product", "Location", "On-Hand Qty"]]
            for p in data["products"]:
                rows.append([p["product_name"], p["location"], f'{p["qty"]:,.2f} {p["unit"]}'])
            elements.append(_make_table(rows, [260, 160, 130], align_right_cols=[2]))

    return _build_pdf_buffer(build)


def pdf_blend_cost(reports):
    from reportlab.platypus import Paragraph, Spacer

    def build(elements):
        styles = _get_report_styles()
        _pdf_header(elements, styles, "Blend Cost Report (Current)", [
            "Priced using each component's current average unit cost",
            f"Generated {now_central_str()}",
        ])
        for f in reports:
            elements.append(Paragraph(f'{f["formula_name"]} — ${f["cost_per_gal"]:,.4f} / gal', styles["SectionHeading"]))
            if f["missing_products"]:
                elements.append(Paragraph(
                    f'<font color="#b00020">Missing component product(s), excluded from cost: {", ".join(f["missing_products"])}</font>',
                    styles["Normal"],
                ))
            rows = [["Component", "Percent", "Current Unit Cost"]]
            for c in f["components"]:
                rows.append([c["product_name"], f'{c["percent"]:.2f}%', f'${c["unit_cost"]:,.4f}'])
            elements.append(_make_table(rows, [250, 100, 130], align_right_cols=[1, 2]))
            elements.append(Spacer(1, 6))

    return _build_pdf_buffer(build)


def build_blend_instruction_report(formula, batch_qty, batch_unit, location_id=None, tank_id=None):
    """
    Everything the Blend Instruction report shows, computed with live inventory.

    Quantities use the same rule as executing a blend (plan_formula_requirements /
    convert_required_to_product_unit): a formula's percentages apply in the unit the
    batch is entered in, so a GAL batch is % by volume and an LB batch is % by weight.
    Each component converts between gal and lbs with its OWN weight (lb/gal).
    """
    warnings = []
    batch_unit = normalize_unit(batch_unit or "gal")
    if batch_unit not in ("gal", "lb"):
        batch_unit = "gal"
        warnings.append("Batch unit must be GAL or LB; using GAL.")
    try:
        batch_qty = float(batch_qty)
    except (TypeError, ValueError):
        batch_qty = 0.0
    if batch_qty <= 0:
        warnings.append("Enter a batch size greater than 0.")
    basis = "volume" if batch_unit == "gal" else "weight"

    locations = load_locations_safe()
    loc = get_location_by_id(locations, location_id) if location_id else None
    loc_name = (loc or {}).get("name")
    if not loc:
        warnings.append("No blend location chosen: on-hand at the blend location can't be checked.")
    tank_name = None
    if tank_id:
        t = get_tank_by_id(load_tanks(), tank_id)
        if not t or str(t.get("location_id")) != str(location_id):
            warnings.append("The selected tank isn't at the selected location.")
        else:
            tank_name = t.get("name") or str(t.get("id"))

    products = load_products()  # live at the moment of printing
    migrate_products_to_layers(products)
    by_id = {str(p.get("id")): p for p in products}
    loc_key = (loc_name or "").strip().lower()

    rows = []
    for c in formula.get("components") or []:
        pid = str(c.get("product_id") or "")
        pct = _safe_float(c.get("percent"), 0.0)
        prod = by_id.get(pid)
        name = (prod or {}).get("name") or f"(missing product {pid})"
        row = {"product_id": pid, "name": name, "percent": pct, "need_gal": None, "need_lb": None,
               "loc_gal": None, "loc_lb": None, "all_gal": None, "all_lb": None,
               "status": "—", "short_gal": None, "short_lb": None}
        rows.append(row)
        if not prod:
            warnings.append(f"The formula uses a product that no longer exists (id {pid}).")
            continue

        w = _safe_float(prod.get("weight"), 0.0)
        part = pct / 100.0 * batch_qty  # this component's share, in the batch unit
        if batch_unit == "gal":
            row["need_gal"] = part
            row["need_lb"] = part * w if w > 0 else None
        else:
            row["need_lb"] = part
            row["need_gal"] = part / w if w > 0 else None
        if w <= 0:
            warnings.append(f"{name} has no weight (lb/gal) set, so its "
                            f"{'lbs' if batch_unit == 'gal' else 'gallons'} can't be worked out.")

        layers = prod.get("layers") or []
        all_qty = sum(float(l.get("qty") or 0.0) for l in layers)
        loc_qty = sum(float(l.get("qty") or 0.0) for l in layers
                      if (l.get("location") or "").strip().lower() == loc_key) if loc else None
        row["all_gal"], row["all_lb"] = _qty_gal_lb(prod, all_qty)
        if loc_qty is not None:
            row["loc_gal"], row["loc_lb"] = _qty_gal_lb(prod, loc_qty)

        # Short / OK against the blend location (that's where a blend pulls from)
        if loc_qty is not None and batch_qty > 0:
            if row["need_gal"] is not None and row["loc_gal"] is not None:
                short = row["need_gal"] - row["loc_gal"]
                row["short_gal"] = short if short > 1e-6 else None
                if row["short_gal"] is not None and w > 0:
                    row["short_lb"] = row["short_gal"] * w
            elif row["need_lb"] is not None and row["loc_lb"] is not None:
                short = row["need_lb"] - row["loc_lb"]
                row["short_lb"] = short if short > 1e-6 else None
            else:
                row["status"] = "CHECK"
                warnings.append(f"{name}: can't compare need vs. on-hand (missing weight or package size).")
                continue
            row["status"] = "SHORT" if (row["short_gal"] or row["short_lb"]) else "OK"

    total_pct = sum(r["percent"] for r in rows)
    sum_gal = sum(r["need_gal"] for r in rows) if all(r["need_gal"] is not None for r in rows) else None
    sum_lb = sum(r["need_lb"] for r in rows) if all(r["need_lb"] is not None for r in rows) else None
    # The batch size in the entered unit is exact; the other unit is what the components add up to.
    batch_gal = batch_qty if batch_unit == "gal" else sum_gal
    batch_lb = batch_qty if batch_unit == "lb" else sum_lb

    if not rows:
        warnings.append("This formula has no components.")
    if abs(total_pct - 100.0) > 0.001:
        warnings.append(f"Percentages add up to {total_pct:.3f}%, not 100%. Fix the formula before blending.")
    entered_sum = sum_gal if batch_unit == "gal" else sum_lb
    if batch_qty > 0 and entered_sum is not None and abs(entered_sum - batch_qty) > 0.001:
        warnings.append(f"Component quantities add up to {entered_sum:,.3f} {batch_unit.upper()}, "
                        f"not the {batch_qty:,.3f} {batch_unit.upper()} batch size.")
    shorts = [r["name"] for r in rows if r["status"] == "SHORT"]

    return {
        "formula": formula, "blend_name": (formula.get("name") or "Blend").strip(),
        "batch_qty": batch_qty, "batch_unit": batch_unit, "batch_gal": batch_gal, "batch_lb": batch_lb,
        "basis": basis, "location_id": location_id, "location_name": loc_name, "tank_name": tank_name,
        "rows": rows, "total_pct": total_pct, "sum_gal": sum_gal, "sum_lb": sum_lb,
        "warnings": warnings, "shorts": shorts,
        "printed_at": now_central_str(),
        "printed_by": user_display_name(current_user() or {}) or "—",
    }


def _bi_num(v, d=2):
    return "—" if v is None else f"{v:,.{d}f}"


def pdf_blend_instruction(rep):
    from reportlab.lib.pagesizes import letter, landscape
    from reportlab.platypus import SimpleDocTemplate, Paragraph, Spacer, Table, TableStyle
    from reportlab.lib import colors
    from reportlab.lib.styles import ParagraphStyle

    styles = _get_report_styles()
    styles.add(ParagraphStyle(name="Warn", fontSize=10, leading=13, textColor=colors.HexColor("#b91c1c"),
                              fontName="Helvetica-Bold"))
    f = rep["formula"]
    elements = []
    where = rep["location_name"] or "(no location chosen)"
    if rep["tank_name"]:
        where += f" — Tank {rep['tank_name']}"
    basis_txt = "BY VOLUME (batch entered in GAL)" if rep["basis"] == "volume" else "BY WEIGHT (batch entered in LBS)"
    _pdf_header(elements, styles, f"Blend Instructions — {rep['blend_name']}", [
        f"<b>Formula:</b> {f.get('name') or '(unnamed)'} &nbsp;(ID {f.get('id')}"
        + (f", updated {str(f.get('updated_at'))[:10]}" if f.get("updated_at") else "") + ")",
        f"<b>Batch size:</b> {_bi_num(rep['batch_gal'])} gal &nbsp;/&nbsp; {_bi_num(rep['batch_lb'])} lbs",
        f"<b>Made at:</b> {where}",
        f"<b>Percentages are {basis_txt}</b>",
        f"<b>Date:</b> {rep['printed_at']} &nbsp;&nbsp; <b>Printed by:</b> {rep['printed_by']}"
        f" &nbsp;&nbsp; <i>Inventory is live as of this time.</i>",
    ])

    for w in rep["warnings"]:
        elements.append(Paragraph("WARNING: " + w, styles["Warn"]))
    if rep["shorts"]:
        elements.append(Paragraph("SHORT on: " + ", ".join(rep["shorts"]) + ". Not enough on hand at "
                                  + (rep["location_name"] or "the blend location") + ".", styles["Warn"]))
    if rep["warnings"] or rep["shorts"]:
        elements.append(Spacer(1, 8))

    hdr = ParagraphStyle(name="BiHead", fontName="Helvetica-Bold", fontSize=8, leading=10, textColor=colors.white)
    hdr_r = ParagraphStyle(name="BiHeadR", parent=hdr, alignment=2)
    cell = ParagraphStyle(name="BiCell", fontName="Helvetica", fontSize=8.5, leading=10.5)
    short_style = ParagraphStyle(name="BiShort", parent=cell, fontName="Helvetica-Bold",
                                 textColor=colors.HexColor("#b91c1c"))
    ok_style = ParagraphStyle(name="BiOk", parent=cell, fontName="Helvetica-Bold", textColor=colors.HexColor("#15803d"))
    at = rep["location_name"] or "location"
    data = [
        [Paragraph("Component", hdr)] + [Paragraph(h, hdr_r) for h in (
            "% of blend", "Need<br/>(gal)", "Need<br/>(lbs)", f"On hand @ {at}<br/>(gal)", f"On hand @ {at}<br/>(lbs)",
            "All locations<br/>(gal)", "All locations<br/>(lbs)")] + [Paragraph("Status", hdr)],
    ]
    for r in rep["rows"]:
        if r["status"] == "SHORT":
            parts = []
            if r["short_gal"] is not None:
                parts.append(f"{_bi_num(r['short_gal'])} gal")
            if r["short_lb"] is not None:
                parts.append(f"{_bi_num(r['short_lb'])} lbs")
            status = Paragraph("SHORT<br/>missing " + "<br/>".join(parts), short_style)
        else:
            status = Paragraph(r["status"], ok_style if r["status"] == "OK" else cell)
        data.append([Paragraph(r["name"], cell), f"{r['percent']:.2f}%", _bi_num(r["need_gal"]), _bi_num(r["need_lb"]),
                     _bi_num(r["loc_gal"]), _bi_num(r["loc_lb"]), _bi_num(r["all_gal"]), _bi_num(r["all_lb"]), status])
    data.append(["TOTAL", f"{rep['total_pct']:.2f}%", _bi_num(rep["sum_gal"]), _bi_num(rep["sum_lb"]),
                 "", "", "", "", ""])

    t = Table(data, colWidths=[140, 56, 64, 72, 76, 80, 70, 76, 86], repeatRows=1)
    style = [
        ("BACKGROUND", (0, 0), (-1, 0), colors.HexColor("#2c3e50")),
        ("TEXTCOLOR", (0, 0), (-1, 0), colors.white),
        ("FONTNAME", (0, 0), (-1, 0), "Helvetica-Bold"),
        ("FONTSIZE", (0, 0), (-1, -1), 8.5),
        ("ROWBACKGROUNDS", (0, 1), (-1, -2), [colors.white, colors.HexColor("#f4f6f8")]),
        ("GRID", (0, 0), (-1, -1), 0.5, colors.HexColor("#d9dee3")),
        ("VALIGN", (0, 0), (-1, -1), "MIDDLE"),
        ("ALIGN", (1, 0), (-2, -1), "RIGHT"),
        ("FONTNAME", (0, -1), (-1, -1), "Helvetica-Bold"),
        ("LINEABOVE", (0, -1), (-1, -1), 1.2, colors.HexColor("#2c3e50")),
        ("TOPPADDING", (0, 0), (-1, -1), 4), ("BOTTOMPADDING", (0, 0), (-1, -1), 4),
    ]
    for i, r in enumerate(rep["rows"], start=1):
        if r["status"] == "SHORT":
            style.append(("BACKGROUND", (0, i), (-1, i), colors.HexColor("#fde2e2")))
    if abs(rep["total_pct"] - 100.0) > 0.001:
        style += [("TEXTCOLOR", (1, -1), (1, -1), colors.HexColor("#b91c1c"))]
    t.setStyle(TableStyle(style))
    elements.append(t)

    elements.append(Spacer(1, 8))
    elements.append(Paragraph(
        "Gal/lbs conversions use each component's own weight per gallon. Totals: percentages must equal 100% and "
        f"component {'gallons' if rep['basis'] == 'volume' else 'pounds'} must equal the batch size.",
        styles["ReportSubtitle"]))
    if f.get("description"):
        elements.append(Spacer(1, 10))
        elements.append(Paragraph("Notes", styles["SectionHeading"]))
        elements.append(Paragraph(f["description"], styles["Normal"]))

    buf = io.BytesIO()
    doc = SimpleDocTemplate(buf, pagesize=landscape(letter), leftMargin=36, rightMargin=36,
                            topMargin=36, bottomMargin=32, title=f"Blend Instructions — {rep['blend_name']}")
    doc.build(elements)
    buf.seek(0)
    return buf


def pdf_cycle_count(rows, location):
    def build(elements):
        styles = _get_report_styles()
        _pdf_header(elements, styles, "Inventory Cycle Count Sheet", [
            _report_scope_line(location, None, None),
            f"Generated {now_central_str()}",
            "System quantities are intentionally left off — count blind, then compare.",
        ])
        table_rows = [["Product", "Location", "Counted Qty", "Unit", "Counted By"]]
        for r in rows:
            table_rows.append([r["product_name"], r["location"], "______________", r["default_unit"], "______________"])
        elements.append(_make_table(table_rows, [170, 100, 110, 60, 110]))

    return _build_pdf_buffer(build)


# -------------------------
# Report Center — routes
# -------------------------

def _pdf_response(buf, filename):
    """Send a report PDF.

    ?download=1 saves it as a file; otherwise it opens in the browser's PDF
    viewer (new tab) so it can be printed or saved from there. Reports are
    opened from inside floating windows (iframes), and some browsers — Safari
    especially — silently drop a download started inside an iframe, so the
    report pages link these outside the window (target=_blank / _top).
    """
    safe = re.sub(r"[^A-Za-z0-9._-]+", "_", filename).strip("_") or "report.pdf"
    if not safe.lower().endswith(".pdf"):
        safe += ".pdf"
    resp = send_file(buf, mimetype="application/pdf",
                     as_attachment=request.args.get("download") == "1",
                     download_name=safe, max_age=0)
    resp.headers["Cache-Control"] = "no-store"  # numbers must be live, never a cached copy
    return resp


@app.route("/reports")
def reports_center():
    return render_template("reports_center.html", app_title=APP_TITLE)


@app.route("/reports/inventory-value")
def report_inventory_value():
    location = request.args.get("location", "ALL")
    start_s = request.args.get("start_date", "")
    end_s = request.args.get("end_date", "")
    data = build_inventory_value_report(location, _parse_report_date(start_s), _parse_report_date(end_s))
    return render_template(
        "report_inventory_value.html", app_title=APP_TITLE,
        locations=_report_location_choices(), selected_location=location,
        start_date=start_s, end_date=end_s, data=data, generated_at=now_central_str(),
    )


@app.route("/reports/inventory-value/pdf")
def report_inventory_value_pdf():
    location = request.args.get("location", "ALL")
    start_s = request.args.get("start_date", "")
    end_s = request.args.get("end_date", "")
    data = build_inventory_value_report(location, _parse_report_date(start_s), _parse_report_date(end_s))
    buf = pdf_inventory_value(data, location, start_s, end_s)
    return _pdf_response(buf, "total_inventory_value.pdf")


@app.route("/reports/avg-cost")
def report_avg_cost():
    location = request.args.get("location", "ALL")
    start_s = request.args.get("start_date", "")
    end_s = request.args.get("end_date", "")
    data = build_avg_cost_report(location, _parse_report_date(start_s), _parse_report_date(end_s))
    return render_template(
        "report_avg_cost.html", app_title=APP_TITLE,
        locations=_report_location_choices(), selected_location=location,
        start_date=start_s, end_date=end_s, data=data, generated_at=now_central_str(),
    )


@app.route("/reports/avg-cost/pdf")
def report_avg_cost_pdf():
    location = request.args.get("location", "ALL")
    start_s = request.args.get("start_date", "")
    end_s = request.args.get("end_date", "")
    data = build_avg_cost_report(location, _parse_report_date(start_s), _parse_report_date(end_s))
    buf = pdf_avg_cost(data, location, start_s, end_s)
    return _pdf_response(buf, "avg_cost_of_goods.pdf")


@app.route("/reports/inventory-listing")
def report_inventory_listing():
    location = request.args.get("location", "ALL")
    start_s = request.args.get("start_date", "")
    end_s = request.args.get("end_date", "")
    data = build_inventory_value_report(location, _parse_report_date(start_s), _parse_report_date(end_s))
    return render_template(
        "report_inventory_listing.html", app_title=APP_TITLE,
        locations=_report_location_choices(), selected_location=location,
        start_date=start_s, end_date=end_s, data=data, generated_at=now_central_str(),
    )


@app.route("/reports/inventory-listing/pdf")
def report_inventory_listing_pdf():
    location = request.args.get("location", "ALL")
    start_s = request.args.get("start_date", "")
    end_s = request.args.get("end_date", "")
    data = build_inventory_value_report(location, _parse_report_date(start_s), _parse_report_date(end_s))
    buf = pdf_inventory_listing(data, location, start_s, end_s, show_costs=can_see_costs())
    return _pdf_response(buf, "total_inventory_report.pdf")


@app.route("/reports/blend-cost")
def report_blend_cost():
    formulas = load_formulas()
    selected = request.args.getlist("formula_id")
    data = build_blend_cost_report(selected or None)
    return render_template(
        "report_blend_cost.html", app_title=APP_TITLE,
        formulas=formulas, selected_ids=selected, data=data, generated_at=now_central_str(),
    )


@app.route("/reports/blend-cost/pdf")
def report_blend_cost_pdf():
    selected = request.args.getlist("formula_id")
    data = build_blend_cost_report(selected or None)
    buf = pdf_blend_cost(data)
    return _pdf_response(buf, "blend_cost_report.pdf")


@app.route("/reports/blend-instruction")
def report_blend_instruction():
    rep, ctx = _blend_instruction_request()
    return render_template("report_blend_instruction.html", app_title=APP_TITLE, rep=rep, **ctx)


@app.route("/reports/blend-instruction/pdf")
def report_blend_instruction_pdf():
    rep, ctx = _blend_instruction_request()
    if not rep:
        flash("Formula not found.", "danger")
        return redirect(url_for("report_blend_instruction"))
    buf = pdf_blend_instruction(rep)
    fname = f'blend_instructions_{rep["blend_name"].replace(" ", "_")}_{rep["batch_qty"]:g}{rep["batch_unit"]}.pdf'
    return _pdf_response(buf, fname)


def _blend_instruction_request():
    """Read the report options from the query string (shared by the page and the PDF)."""
    formulas = load_formulas()
    formula_id = request.args.get("formula_id") or (formulas[0]["id"] if formulas else None)
    formula = get_formula_by_id(formulas, formula_id) if formula_id else None
    allowed = allowed_location_ids(current_user())
    locations = [l for l in load_locations_safe() if allowed is None or str(l.get("id")) in allowed]
    defaults = (formula or {}).get("defaults") or {}
    batch_unit = normalize_unit(request.args.get("batch_unit") or defaults.get("target_unit") or "gal")
    batch_qty = request.args.get("batch_qty") or defaults.get("target_qty") or 100
    location_id = request.args.get("location_id") or (str(locations[0]["id"]) if locations else None)
    tank_id = request.args.get("tank_id") or None
    tanks = [t for t in load_tanks() if t.get("is_active", True)]
    rep = build_blend_instruction_report(formula, batch_qty, batch_unit, location_id, tank_id) if formula else None
    ctx = {"formulas": formulas, "formula": formula, "locations": locations, "tanks": tanks,
           "sel": {"formula_id": formula_id, "batch_qty": batch_qty, "batch_unit": batch_unit,
                   "location_id": location_id, "tank_id": tank_id}}
    return rep, ctx


@app.route("/reports/cycle-count")
def report_cycle_count():
    location = request.args.get("location", "ALL")
    count = request.args.get("count", "10")
    rows = build_cycle_count_sheet(location, count)
    return render_template(
        "report_cycle_count.html", app_title=APP_TITLE,
        locations=_report_location_choices(), selected_location=location,
        count=count, rows=rows, generated_at=now_central_str(),
    )


@app.route("/reports/cycle-count/pdf")
def report_cycle_count_pdf():
    location = request.args.get("location", "ALL")
    count = request.args.get("count", "10")
    rows = build_cycle_count_sheet(location, count)
    buf = pdf_cycle_count(rows, location)
    return _pdf_response(buf, "cycle_count_sheet.pdf")


# -------------------------
# Startup cleanup
# -------------------------
def canonicalize_products_on_startup():
    products = load_products()
    alerts = load_alerts()

    products_changed = False
    alerts_changed = False

    # --- Normalize product default_unit to ALL CAPS ---
    for p in products:
        u = p.get("default_unit")
        canon_display = unit_to_display(u)
        if canon_display and canon_display != p.get("default_unit"):
            p["default_unit"] = canon_display
            products_changed = True

    # Ensure layers exist (and sync qty/cost)
    if migrate_products_to_layers(products):
        products_changed = True

    # --- Normalize alerts threshold_unit to ALL CAPS ---
    for a in alerts:
        unit = a.get("threshold_unit")
        if isinstance(unit, str) and unit != unit.upper():
            a["threshold_unit"] = unit.upper()
            alerts_changed = True

    # --- Save only what actually changed ---
    if products_changed:
        save_products(products)
    if alerts_changed:
        save_alerts(alerts)




# ---------------------------------------------------------------------------
# Transaction History + Undo
# ---------------------------------------------------------------------------
# Every request that moves inventory is wrapped: the stock stores are
# snapshotted before the route runs and again after, and the exact difference
# (bulk FIFO layers per product/location/cost, package rows, tank rows,
# staging and blend-log records) is saved as ONE transaction record.
#
# Undo never deletes anything. It writes a reversing transaction linked to the
# original, appends opposite package/tank rows, puts bulk stock back exactly
# where it came from, and marks the original "undone" with who/when/why.
# All files an undo touches are written together in one commit (see
# _commit_files), so a blend's parts reverse all-or-nothing.
# ---------------------------------------------------------------------------
import copy
import threading
from contextlib import contextmanager
from flask import g

try:
    import fcntl
except ImportError:  # Windows dev machines: thread lock only
    fcntl = None

TRANSACTIONS_PATH = os.path.join(DATA_DIR, "transactions.json")
COMMIT_JOURNAL_PATH = os.path.join(DATA_DIR, ".commit_journal.json")
INVENTORY_LOCK_PATH = os.path.join(DATA_DIR, ".inventory.lock")

TXN_EPS = 1e-6
TXN_ACTIONS = ["Receive", "Remove", "Move", "Repackage", "Blend", "Staging", "Staging Release",
               "Staging Cancel", "Undo"]

# Routes that move stock (POST only). Anything they change is logged.
TXN_ENDPOINTS = {
    "inventory_adjust_page", "inventory_add_page", "inventory_receive_page", "receive_inventory",
    "blend_build", "blend_execute_formula", "blend_execute_at_location",
    "staging_create_route", "staging_release_flow", "staging_void_route",
    "staging_picked_up", "staging_cancel",
}


class UndoError(Exception):
    pass


def load_transactions():
    return load_json(TRANSACTIONS_PATH, [])


def next_transaction_id(txns):
    n = 0
    for t in txns:
        tid = str(t.get("id", ""))
        if tid.startswith("TXN-") and tid[4:].isdigit():
            n = max(n, int(tid[4:]))
    return f"TXN-{n + 1:06d}"


def user_can_undo(user) -> bool:
    """Per-user switch, on unless an admin turned it off."""
    return bool(user) and normalize_user(user).get("can_undo", True) is not False


# ---- One lock for every stock write (threads + gunicorn workers) ----
_inventory_thread_lock = threading.Lock()


def _inventory_lock_acquire():
    _inventory_thread_lock.acquire()
    fh = None
    if fcntl:
        try:
            _ensure_dir_for(INVENTORY_LOCK_PATH)
            fh = open(INVENTORY_LOCK_PATH, "a")
            fcntl.flock(fh, fcntl.LOCK_EX)
        except Exception:
            fh = None
    return fh


def _inventory_lock_release(fh):
    try:
        if fh is not None:
            fcntl.flock(fh, fcntl.LOCK_UN)
            fh.close()
    finally:
        _inventory_thread_lock.release()


@contextmanager
def inventory_lock():
    fh = _inventory_lock_acquire()
    try:
        yield
    finally:
        _inventory_lock_release(fh)


# ---- All-or-nothing multi-file write ----
def _commit_files(files: dict):
    """
    Write several JSON files as one unit. Every new version is written and
    fsynced to a temp file first; then a journal listing them is saved; then
    each temp file is swapped in. If the app dies partway through the swaps,
    _recover_commit_journal() finishes them on the next start, so the files
    never end up half-updated.
    """
    staged = {}
    try:
        for path, data in files.items():
            _ensure_dir_for(path)
            fd, tmp = tempfile.mkstemp(prefix=".commit_", suffix=".json", dir=os.path.dirname(path))
            with os.fdopen(fd, "w", encoding="utf-8") as f:
                json.dump(data, f, indent=2)
                f.flush()
                os.fsync(f.fileno())
            staged[path] = tmp
    except Exception:
        for tmp in staged.values():
            try:
                os.remove(tmp)
            except OSError:
                pass
        raise
    _atomic_write_json(COMMIT_JOURNAL_PATH, staged)
    _recover_commit_journal()


def _recover_commit_journal():
    if not os.path.exists(COMMIT_JOURNAL_PATH):
        return
    try:
        with open(COMMIT_JOURNAL_PATH, "r", encoding="utf-8") as f:
            staged = json.load(f)
    except Exception:
        staged = {}
    for path, tmp in (staged or {}).items():
        if os.path.exists(tmp):
            os.replace(tmp, path)
    os.remove(COMMIT_JOURNAL_PATH)


_recover_commit_journal()


def _build_ledger_entry(entries: list, event_type: str, payload: dict) -> dict:
    prev_hash = entries[-1]["entry_hash"] if entries else GENESIS_HASH
    entry_id = f"LEDG-{len(entries) + 1:07d}"
    timestamp = now_central_iso()
    entry = {"entry_id": entry_id, "prev_hash": prev_hash, "event_type": event_type,
             "timestamp": timestamp, "payload": payload}
    entry["entry_hash"] = _hash_entry(prev_hash, entry_id, event_type, timestamp, payload)
    return entry


# ---- Snapshot + diff ----
def _layer_key(layer):
    return (str(layer.get("location") or ""), round(float(layer.get("unit_cost") or 0.0), 4),
            str(layer.get("datetime") or ""))


def _txn_snapshot():
    products = copy.deepcopy(load_products())
    migrate_products_to_layers(products)  # same normalizing the routes do, so it never shows as a change
    prods = {}
    for p in products:
        if not isinstance(p, dict):
            continue
        layers = {}
        for l in p.get("layers") or []:
            k = _layer_key(l)
            layers[k] = layers.get(k, 0.0) + float(l.get("qty") or 0.0)
        prods[str(p.get("id"))] = {
            "name": p.get("name"), "default_unit": normalize_unit(p.get("default_unit")),
            "weight": p.get("weight"), "package_size_gal": p.get("package_size_gal"), "layers": layers,
        }
    return {
        "products": prods,
        "pki": {str(r.get("id")): r for r in load_package_inventory()},
        "tank_ledger": {str(r.get("id")): r for r in load_tank_ledger()},
        "staging": {str(r.get("id")): r for r in load_staging()},
        "blends": {str(r.get("id")): r for r in load_blends()},
    }


def _txn_diff(before, after):
    bulk = []
    for pid in sorted(set(before["products"]) | set(after["products"])):
        b = before["products"].get(pid, {}).get("layers", {})
        a = after["products"].get(pid, {}).get("layers", {})
        info = after["products"].get(pid) or before["products"].get(pid)
        for key in set(a) | set(b):
            d = a.get(key, 0.0) - b.get(key, 0.0)
            if abs(d) > TXN_EPS:
                bulk.append({"product_id": pid, "product_name": info["name"], "unit": info["default_unit"],
                             "location": key[0], "unit_cost": key[1], "datetime": key[2], "qty": round(d, 4)})
    bulk.sort(key=lambda e: (e["qty"] > 0, e["product_name"] or "", e["location"]))

    staging = []
    for sid, rec in after["staging"].items():
        old = before["staging"].get(sid)
        if old is None:
            staging.append({"id": sid, "new": True, "status_after": rec.get("status"),
                            "product_id": rec.get("product_id"), "product_name": rec.get("product_name"),
                            "location_name": rec.get("location_name"), "qty_default": rec.get("qty_default"),
                            "default_unit": rec.get("default_unit")})
            continue
        changed = sorted(k for k in set(rec) | set(old) if rec.get(k) != old.get(k) or (k in rec) != (k in old))
        if changed:
            staging.append({"id": sid, "new": False,
                            "before": {k: old[k] for k in changed if k in old},
                            "after": {k: rec[k] for k in changed if k in rec},
                            "product_id": rec.get("product_id"), "product_name": rec.get("product_name"),
                            "location_name": rec.get("location_name"), "qty_default": rec.get("qty_default"),
                            "default_unit": rec.get("default_unit")})

    return {
        "bulk": bulk,
        "pki": [r for k, r in after["pki"].items() if k not in before["pki"]],
        "tank": [r for k, r in after["tank_ledger"].items() if k not in before["tank_ledger"]],
        "staging": staging,
        "blends": [{"id": k, "number": r.get("number"), "blend": r.get("blend")}
                   for k, r in after["blends"].items() if k not in before["blends"]],
        "new_products": [pid for pid in after["products"] if pid not in before["products"]],
    }


def _txn_has_changes(eff):
    return any(eff.get(k) for k in ("bulk", "pki", "tank", "staging", "blends"))


def _qty_gal_lb(info, qty):
    """(gallons, pounds) for a qty in the product's own unit; None where it can't be worked out."""
    unit = normalize_unit((info or {}).get("default_unit") or (info or {}).get("unit"))
    w = _safe_float((info or {}).get("weight"), 0.0)
    ps = _safe_float((info or {}).get("package_size_gal"), 0.0)
    gal = lb = None
    if unit == "gal":
        gal = qty
    elif unit == "lb":
        lb = qty
        gal = qty / w if w > 0 else None
    elif unit == "unit" and ps > 0:
        gal = qty * ps
    if lb is None and gal is not None and w > 0:
        lb = gal * w
    return gal, lb


def _tank_location_names():
    locs = {str(l.get("id")): l.get("name") for l in load_locations_safe()}
    return {str(t.get("id")): (locs.get(str(t.get("location_id"))), t.get("name")) for t in load_tanks()}


def _txn_summary(action, eff, prods):
    """Row fields shown in Transaction History (worked out once, when recorded)."""
    tank_locs = _tank_location_names()
    locations = []

    def add_loc(name):
        if name and name not in locations:
            locations.append(name)

    for e in eff["bulk"]:
        add_loc(e["location"])
    for r in eff["pki"]:
        add_loc(r.get("location_name"))
    for r in eff["tank"]:
        add_loc(tank_locs.get(str(r.get("tank_id")), (None, None))[0])
    for s in eff["staging"]:
        add_loc(s.get("location_name"))

    pos, neg = {}, {}
    for e in eff["bulk"]:
        bucket = pos if e["qty"] > 0 else neg
        bucket[e["product_id"]] = bucket.get(e["product_id"], 0.0) + abs(e["qty"])
    if action in ("Remove", "Staging"):
        primary = neg or pos
    else:
        primary = pos or neg

    names, gal_total, lb_total, product_ids = [], 0.0, 0.0, []
    gal_ok = lb_ok = bool(primary)
    for pid, q in primary.items():
        info = prods.get(pid) or {}
        names.append(info.get("name") or pid)
        product_ids.append(pid)
        gal, lb = _qty_gal_lb(info, q)
        if gal is None:
            gal_ok = False
        else:
            gal_total += gal
        if lb is None:
            lb_ok = False
        else:
            lb_total += lb

    if not primary and eff["staging"]:  # e.g. Staging Release: no stock moves, just the order
        s = eff["staging"][0]
        info = prods.get(str(s.get("product_id"))) or {"default_unit": s.get("default_unit")}
        names = [s.get("product_name") or s.get("product_id")]
        product_ids = [str(s.get("product_id"))]
        gal, lb = _qty_gal_lb(info, _safe_float(s.get("qty_default"), 0.0))
        gal_ok, lb_ok = gal is not None, lb is not None
        gal_total, lb_total = gal or 0.0, lb or 0.0

    for r in eff["pki"]:  # products that only changed as packages
        pid = str(r.get("product_id"))
        if pid not in product_ids:
            product_ids.append(pid)
            if not primary:
                names.append((prods.get(pid) or {}).get("name") or pid)

    pkg_types = []
    pkg_count = 0.0
    for r in eff["pki"]:
        if r.get("package_name") and r.get("package_name") not in pkg_types:
            pkg_types.append(r.get("package_name"))
        pkg_count += abs(_safe_float(r.get("quantity"), 0.0))

    loc_display = " → ".join(locations) if action == "Move" and len(locations) == 2 else ", ".join(locations)
    return {
        "location": loc_display, "locations": locations,
        "product": ", ".join(n for n in names if n), "product_ids": product_ids,
        "qty_gal": round(gal_total, 4) if gal_ok else None,
        "qty_lb": round(lb_total, 4) if lb_ok else None,
        "package_type": ", ".join(pkg_types), "package_count": round(pkg_count, 4) if pkg_count else None,
    }


def _txn_action_label(endpoint, form):
    if endpoint in ("inventory_adjust_page", "inventory_add_page"):
        a = (form.get("action") or "add").strip().lower()
        if a == "remove":
            staged = (form.get("stage") or "").lower() in ("1", "true", "yes", "on")
            return "Staging" if staged else "Remove"
        return {"add": "Receive", "move": "Move", "repackage": "Repackage"}.get(a, "Receive")
    if endpoint in ("inventory_receive_page", "receive_inventory"):
        return "Receive"
    if endpoint.startswith("blend_"):
        return "Blend"
    if endpoint == "staging_create_route":
        return "Staging"
    if endpoint in ("staging_release_flow", "staging_picked_up"):
        return "Staging Release"
    return "Staging Cancel"


@app.before_request
def _txn_begin():
    # Registered after the login/permission/CSRF/location checks, so it only
    # runs for requests that are allowed through.
    if request.method != "POST" or request.endpoint not in TXN_ENDPOINTS:
        return None
    user = current_user()
    if not user:
        return None
    g._txn_lock = _inventory_lock_acquire()
    g._txn_active = True
    try:
        g._txn = {
            "before": _txn_snapshot(),
            "action": _txn_action_label(request.endpoint, request.get_json(silent=True) or request.form),
            "user": user.get("username"), "user_id": user.get("id"),
        }
    except Exception:
        g._txn = None
        app.logger.exception("Transaction snapshot failed")
    return None


@app.teardown_request
def _txn_end(exc):
    if not getattr(g, "_txn_active", False):
        return
    try:
        t = getattr(g, "_txn", None)
        if t:
            after = _txn_snapshot()
            eff = _txn_diff(t["before"], after)
            if _txn_has_changes(eff):
                txns = load_transactions()
                rec = {
                    "id": next_transaction_id(txns), "ts": now_central_iso(),
                    "user": t["user"], "user_id": t["user_id"], "action": t["action"],
                    "status": "completed", "summary": _txn_summary(t["action"], eff, after["products"]),
                    "effects": eff, "undo": None, "reverses": None,
                }
                txns.append(rec)
                save_json(TRANSACTIONS_PATH, txns)
                append_ledger_entry("inventory_transaction", {
                    "transaction_id": rec["id"], "action": rec["action"], "by": rec["user"],
                    "location": rec["summary"]["location"], "product": rec["summary"]["product"],
                    "qty_gal": rec["summary"]["qty_gal"],
                })
    except Exception:
        app.logger.exception("Recording the transaction failed")
    finally:
        g._txn_active = False
        _inventory_lock_release(getattr(g, "_txn_lock", None))


# ---- Undo ----
def _bulk_on_hand(prod, location):
    key = (location or "").strip().lower()
    return sum(float(l["qty"]) for l in prod["layers"] if (l.get("location") or "").strip().lower() == key)


def _bulk_put_back(prod, e):
    """Return stock that the original transaction took out, at its original location and cost."""
    key = (e["location"], e["unit_cost"], e["datetime"])
    qty = -e["qty"]
    for l in prod["layers"]:
        if _layer_key(l) == key:
            l["qty"] = round(float(l["qty"]) + qty, 4)
            return
    new = {"qty": round(qty, 4), "unit": normalize_unit(prod.get("default_unit")), "unit_cost": e["unit_cost"],
           "datetime": e["datetime"], "location": e["location"]}
    # keep FIFO order: in front of the first layer that's newer
    idx = next((i for i, l in enumerate(prod["layers"]) if str(l.get("datetime") or "") > e["datetime"]),
               len(prod["layers"]))
    prod["layers"].insert(idx, new)


def _bulk_take_out(prod, e):
    """Remove stock the original transaction added: that exact layer first, then oldest at the same location."""
    need = e["qty"]
    key = (e["location"], e["unit_cost"], e["datetime"])
    loc = e["location"].strip().lower()
    order = [l for l in prod["layers"] if _layer_key(l) == key] + \
            [l for l in prod["layers"] if _layer_key(l) != key and (l.get("location") or "").strip().lower() == loc]
    for l in order:
        if need <= TXN_EPS:
            break
        take = min(float(l["qty"]), need)
        l["qty"] = float(l["qty"]) - take
        need -= take
    prod["layers"] = [l for l in prod["layers"] if float(l["qty"]) > 1e-9]


def _pki_count(records, product_id, package_id, location_id):
    return sum(_safe_float(r.get("quantity"), 0.0) for r in records
               if str(r.get("product_id")) == str(product_id) and str(r.get("package_id")) == str(package_id)
               and str(r.get("location_id")) == str(location_id))


def _fmt_qty(q, unit):
    return f"{q:,.4f}".rstrip("0").rstrip(".") + f" {str(unit or '').upper()}"


def undo_preview(txn, products_by_id=None, pki=None, tank_rows=None, tanks=None):
    """The exact stock changes an undo would make, as rows for the confirmation pop-up."""
    products_by_id = products_by_id if products_by_id is not None else {str(p.get("id")): p for p in load_products()}
    pki = pki if pki is not None else load_package_inventory()
    tank_rows = tank_rows if tank_rows is not None else load_tank_ledger()
    tanks = tanks if tanks is not None else load_tanks()
    eff = txn.get("effects") or {}
    rows = []

    # bulk, netted per product + location
    net = {}
    for e in eff.get("bulk", []):
        k = (e["product_id"], e["location"])
        net[k] = net.get(k, 0.0) - e["qty"]
    for (pid, loc), change in net.items():
        if abs(change) <= TXN_EPS:
            continue
        p = products_by_id.get(pid)
        unit = normalize_unit((p or {}).get("default_unit"))
        now = _bulk_on_hand({"layers": (p or {}).get("layers") or []}, loc) if p else 0.0
        rows.append({"kind": "Bulk", "item": (p or {}).get("name") or pid, "location": loc,
                     "change": ("+" if change > 0 else "−") + _fmt_qty(abs(change), unit),
                     "now": _fmt_qty(now, unit), "after": _fmt_qty(now + change, unit),
                     "problem": now + change < -TXN_EPS})

    for r in eff.get("pki", []):
        q = -_safe_float(r.get("quantity"), 0.0)
        now = _pki_count(pki, r.get("product_id"), r.get("package_id"), r.get("location_id"))
        name = (products_by_id.get(str(r.get("product_id"))) or {}).get("name") or r.get("product_id")
        rows.append({"kind": "Packages", "item": f"{name} — {r.get('package_name')}",
                     "location": r.get("location_name"), "change": f"{'+' if q > 0 else '−'}{abs(q):g}",
                     "now": f"{now:g}", "after": f"{now + q:g}", "problem": now + q < -TXN_EPS})

    tank_names = _tank_location_names()
    for r in eff.get("tank", []):
        d = -_safe_float(r.get("delta_gal"), 0.0)
        tid = str(r.get("tank_id"))
        now = get_tank_fill_gal(tank_rows, tid)
        t = get_tank_by_id(tanks, tid) or {}
        cap = _safe_float(t.get("capacity_gal"), 0.0)
        loc, tname = tank_names.get(tid, (None, tid))
        rows.append({"kind": "Tank", "item": tname or tid, "location": loc,
                     "change": f"{'+' if d > 0 else '−'}{abs(d):g} GAL", "now": f"{now:g} GAL",
                     "after": f"{now + d:g} GAL",
                     "problem": now + d < -TXN_EPS or (cap > 0 and now + d > cap + TXN_EPS)})

    for s in eff.get("staging", []):
        if s.get("new"):
            rows.append({"kind": "Staging", "item": s.get("product_name"), "location": s.get("location_name"),
                         "change": "Order marked undone", "now": s.get("status_after"), "after": "undone",
                         "problem": False})
        else:
            rows.append({"kind": "Staging", "item": s.get("product_name"), "location": s.get("location_name"),
                         "change": "Order set back", "now": (s.get("after") or {}).get("status", "—"),
                         "after": (s.get("before") or {}).get("status", "—"), "problem": False})
    for b in eff.get("blends", []):
        rows.append({"kind": "Blend log", "item": f"Blend #{b.get('number')} {b.get('blend') or ''}".strip(),
                     "location": "", "change": "Marked undone", "now": "", "after": "", "problem": False})
    return rows


def undo_transaction(txn_id: str, user: dict, reason: str | None):
    """Reverse one transaction. Raises UndoError (and changes nothing) if it can't."""
    txns = load_transactions()
    txn = next((t for t in txns if t.get("id") == txn_id), None)
    if not txn:
        raise UndoError("That transaction wasn't found.")
    if txn.get("reverses"):
        raise UndoError("This entry is itself an undo and can't be undone.")
    if txn.get("status") == "undone":
        raise UndoError(f"{txn_id} was already undone.")
    for loc in (txn.get("summary") or {}).get("locations") or []:
        if not user_can_use_location(user, loc_name=loc):
            raise UndoError(f"You aren't assigned to {loc}.")

    eff = txn.get("effects") or {}
    errors = []
    now = now_central_iso()
    who = user.get("username")

    # 1) bulk stock: put back what was taken, then take out what was added
    products = load_products()
    migrate_products_to_layers(products)
    by_id = {str(p.get("id")): p for p in products}
    touched = set()
    for e in [e for e in eff.get("bulk", []) if e["qty"] < 0]:
        prod = by_id.get(e["product_id"])
        if not prod:
            errors.append(f"{e['product_name']} no longer exists.")
            continue
        _bulk_put_back(prod, e)
        touched.add(e["product_id"])
    for e in [e for e in eff.get("bulk", []) if e["qty"] > 0]:
        prod = by_id.get(e["product_id"])
        if not prod:
            errors.append(f"{e['product_name']} no longer exists.")
            continue
        have = _bulk_on_hand(prod, e["location"])
        if have + TXN_EPS < e["qty"]:
            errors.append(f"{prod.get('name')} at {e['location']}: only {_fmt_qty(have, e['unit'])} on hand, "
                          f"undo needs to remove {_fmt_qty(e['qty'], e['unit'])} (stock would go negative).")
            continue
        _bulk_take_out(prod, e)
        touched.add(e["product_id"])
    for pid in touched:
        _sync_product_qty_and_avg_cost_from_layers(by_id[pid])
        by_id[pid]["last_updated"] = now

    # 2) package counts: opposite rows
    pki = load_package_inventory()
    pki_keys = set()
    for r in eff.get("pki", []):
        q = -_safe_float(r.get("quantity"), 0.0)
        vol = _safe_float(r.get("volume_per"), 0.0)
        pki.append({**r, "id": generate_next_pki_id(pki), "quantity": q, "total_volume": q * vol,
                    "received_at": now if q > 0 else None, "removed_at": now if q < 0 else None,
                    "type": "undo", "notes": f"Undo of {txn_id}"})
        pki_keys.add((r.get("product_id"), r.get("package_id"), r.get("location_id"), r.get("package_name")))
    for pid, pkg, lid, pname in pki_keys:
        left = _pki_count(pki, pid, pkg, lid)
        if left < -TXN_EPS:
            name = (by_id.get(str(pid)) or {}).get("name") or pid
            errors.append(f"{name} {pname}: package count would go negative ({left:g}).")

    # 3) tanks: opposite rows, then check fill/capacity/which product the tank holds
    tank_rows = load_tank_ledger()
    tanks = load_tanks()
    tank_in = {}
    for r in eff.get("tank", []):
        d = -_safe_float(r.get("delta_gal"), 0.0)
        tank_rows.append({"id": generate_next_tx_id(tank_rows), "ts": now, "tank_id": str(r.get("tank_id")),
                          "product_id": r.get("product_id"), "delta_gal": d, "source": "undo",
                          "ref": txn_id, "notes": f"Undo of {txn_id}"})
        if d > 0:
            tank_in[str(r.get("tank_id"))] = r.get("product_id")
    for tid in {str(r.get("tank_id")) for r in eff.get("tank", [])}:
        t = get_tank_by_id(tanks, tid)
        fill = get_tank_fill_gal(tank_rows, tid)
        name = (t or {}).get("name") or tid
        if fill < -TXN_EPS:
            errors.append(f"Tank {name} would go below empty ({fill:g} gal).")
        cap = _safe_float((t or {}).get("capacity_gal"), 0.0)
        if t and cap > 0 and fill > cap + TXN_EPS:
            errors.append(f"Tank {name} would be over capacity ({fill:g} of {cap:g} gal).")
        if t and tid in tank_in:
            holds = t.get("assigned_product_id")
            if holds and str(holds) != str(tank_in[tid]):
                errors.append(f"Tank {name} now holds a different product.")
        if t:
            if fill <= 1e-9:
                t["assigned_product_id"] = None
            elif not t.get("assigned_product_id") and tid in tank_in:
                t["assigned_product_id"] = tank_in[tid]

    # 4) staging orders: only if nothing has changed them since
    staging = load_staging()
    st_by_id = {str(r.get("id")): r for r in staging}
    for s in eff.get("staging", []):
        rec = st_by_id.get(str(s["id"]))
        label = s.get("product_name") or "staging order"
        if not rec:
            errors.append(f"The staging order for {label} no longer exists.")
            continue
        if s.get("new"):
            if rec.get("status") != s.get("status_after"):
                errors.append(f"The staging order for {label} is now '{rec.get('status')}'. Undo that change first.")
                continue
            rec.update({"status": "undone", "undone_at": now, "undone_by": who, "undone_txn": txn_id})
        else:
            after, before = s.get("after") or {}, s.get("before") or {}
            keys = set(after) | set(before)
            if any(rec.get(k) != after.get(k) or (k in rec) != (k in after) for k in keys):
                errors.append(f"The staging order for {label} has changed since. Undo the later change first.")
                continue
            for k in keys:
                if k in before:
                    rec[k] = before[k]
                else:
                    rec.pop(k, None)

    # 5) blend log entries
    blends = load_blends()
    bl_by_id = {str(b.get("id")): b for b in blends}
    for b in eff.get("blends", []):
        rec = bl_by_id.get(str(b["id"]))
        if rec:
            rec.update({"status": "undone", "undone_at": now, "undone_by": who, "undo_reason": reason,
                        "undone_txn": txn_id})

    if errors:
        raise UndoError("Can't undo " + txn_id + ": " + " ".join(errors))

    # 6) the reversing entry + mark the original
    rev_id = next_transaction_id(txns)
    rev_eff = {
        "bulk": [{**e, "qty": -e["qty"]} for e in eff.get("bulk", [])],
        "pki": [r for r in pki if r.get("type") == "undo" and r.get("notes") == f"Undo of {txn_id}"],
        "tank": [r for r in tank_rows if r.get("source") == "undo" and r.get("ref") == txn_id],
        "staging": eff.get("staging", []), "blends": eff.get("blends", []), "new_products": [],
    }
    txns.append({
        "id": rev_id, "ts": now, "user": who, "user_id": user.get("id"), "action": "Undo",
        "status": "reversal", "summary": dict(txn.get("summary") or {}), "effects": rev_eff,
        "undo": None, "reverses": txn_id, "reverses_action": txn.get("action"), "reason": reason,
    })
    txn["status"] = "undone"
    txn["undo"] = {"by": who, "at": now, "reason": reason, "reversal_id": rev_id}

    ledger = load_ledger()
    ledger.append(_build_ledger_entry(ledger, "inventory_undo", {
        "transaction_id": txn_id, "reversal_id": rev_id, "action": txn.get("action"),
        "by": who, "reason": reason,
    }))

    # 7) everything lands together or not at all
    files = {TRANSACTIONS_PATH: txns, EVENT_LEDGER_PATH: ledger}
    if touched:
        files[DATA_PATH] = products
    if eff.get("pki"):
        files[PACKAGE_INVENTORY_PATH] = pki
    if eff.get("tank"):
        files[TANK_LEDGER_PATH] = tank_rows
        files[TANKS_PATH] = tanks
    if eff.get("staging"):
        files[STAGING_PATH] = staging
    if eff.get("blends"):
        files[BLENDS_PATH] = blends
    _commit_files(files)
    return rev_id


# ---- Pages ----
def _txn_dt(ts):
    try:
        d = datetime.fromisoformat(str(ts))
        return d.strftime("%b %d, %Y"), d.strftime("%I:%M %p").lstrip("0")
    except Exception:
        return str(ts or "")[:10], str(ts or "")[11:16]


@app.route("/transactions")
def transactions_page():
    user = current_user()
    txns = load_transactions()
    allowed = allowed_location_ids(user)
    if allowed is not None:
        txns = [t for t in txns
                if all(user_can_use_location(user, loc_name=l) for l in (t.get("summary") or {}).get("locations") or [])]

    f = {k: (request.args.get(k) or "").strip() for k in ("date_from", "date_to", "user", "location", "action", "product")}
    users = sorted({t.get("user") for t in txns if t.get("user")})
    locations = sorted({l for t in txns for l in (t.get("summary") or {}).get("locations") or []})
    products_by_id = {str(p.get("id")): p for p in load_products()}
    product_choices = sorted({pid for t in txns for pid in (t.get("summary") or {}).get("product_ids") or []},
                             key=lambda pid: ((products_by_id.get(pid) or {}).get("name") or pid).lower())
    product_choices = [(pid, (products_by_id.get(pid) or {}).get("name") or pid) for pid in product_choices]

    def keep(t):
        s = t.get("summary") or {}
        day = str(t.get("ts") or "")[:10]
        if f["date_from"] and day < f["date_from"]:
            return False
        if f["date_to"] and day > f["date_to"]:
            return False
        if f["user"] and t.get("user") != f["user"]:
            return False
        if f["location"] and f["location"] not in (s.get("locations") or []):
            return False
        if f["action"] and t.get("action") != f["action"]:
            return False
        if f["product"] and f["product"] not in (s.get("product_ids") or []):
            return False
        return True

    rows = [t for t in txns if keep(t)]
    rows.sort(key=lambda t: t.get("id") or "", reverse=True)
    total = len(rows)
    rows = rows[:500]

    may_undo = user_can_undo(user)
    pki, tank_rows, tanks = load_package_inventory(), load_tank_ledger(), load_tanks()
    view = []
    for t in rows:
        d, tm = _txn_dt(t.get("ts"))
        can_undo_row = may_undo and t.get("status") == "completed" and not t.get("reverses")
        view.append({
            "t": t, "date": d, "time": tm, "s": t.get("summary") or {},
            "can_undo": can_undo_row,
            "preview": undo_preview(t, products_by_id, pki, tank_rows, tanks) if can_undo_row else None,
        })
    return render_template("transactions.html", app_title=APP_TITLE, rows=view, total=total, f=f,
                           users=users, locations=locations, products=product_choices, actions=TXN_ACTIONS)


@app.post("/transactions/<txn_id>/undo")
def transaction_undo(txn_id):
    user = current_user()
    back = request.form.get("next") or ""
    if not back.startswith("/transactions"):
        back = url_for("transactions_page")
    if not user_can_undo(user):
        return render_template("no_access.html", message="You don't have permission to undo transactions."), 403
    reason = (request.form.get("reason") or "").strip()[:500] or None
    try:
        with inventory_lock():
            rev_id = undo_transaction(txn_id, user, reason)
    except UndoError as e:
        flash(str(e), "danger")
        return redirect(back)
    flash(f"{txn_id} was undone. The reversal is recorded as {rev_id}.", "success")
    return redirect(back)


@app.post("/admin/users/<user_id>/can-undo")
def admin_user_can_undo(user_id):
    me = current_user()
    users = load_users()
    u = next((x for x in users if x.get("id") == user_id), None)
    if not u:
        flash("User not found.", "danger")
        return redirect(url_for("admin_page"))
    u["can_undo"] = request.form.get("can_undo") == "1"
    save_users(users)
    append_ledger_entry("user_can_undo_changed", {"username": u.get("username"), "can_undo": u["can_undo"],
                                                  "by": me.get("username")})
    flash(f"{user_display_name(u)} {'can' if u['can_undo'] else 'can no longer'} undo transactions.", "success")
    return redirect(url_for("admin_page"))


# -------------------------
# Entrypoint
# -------------------------
if __name__ == "__main__":
    ensure_data_store()
    ensure_locations_store()
    ensure_tanks_store()
    ensure_tank_ledger_store()
    ensure_formulas_store()
    ensure_packages_store()
    ensure_package_inventory_store()


    canonicalize_products_on_startup()

    products = load_products()
    if migrate_products_to_layers(products):
        save_products(products)

    app.run(debug=os.environ.get("FLASK_DEBUG") == "1")