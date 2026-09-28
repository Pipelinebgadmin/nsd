# utils_display.py
from typing import Optional, Tuple
from utils_units import normalize_unit

def compute_display_breakdown(p) -> Tuple[Optional[float], Optional[float]]:
    """
    Returns (gallons, pounds) for display. 'unit' products return (None, None).
    Assumes p.quantity is in p.default_unit and p.weight is lb/gal if present.
    """
    unit = normalize_unit(getattr(p, "default_unit", ""))
    qty_raw = getattr(p, "quantity", 0) or 0
    try:
        qty = float(qty_raw)
    except Exception:
        qty = 0.0

    wpg = getattr(p, "weight", None)  # lb per gallon (density)
    try:
        wpg_val = float(wpg) if wpg not in (None, "") else None
    except Exception:
        wpg_val = None

    gallons = pounds = None

    if unit == "gal":
        gallons = qty
        if wpg_val:
            pounds = round(qty * wpg_val, 2)
    elif unit == "lb":
        pounds = qty
        if wpg_val and wpg_val != 0:
            gallons = round(qty / wpg_val, 2)
    elif unit == "unit":
        # Do not convert “unit” items (totes, drums, coolers, etc.)
        pass
    else:
        # Fallback: if explicitly liquid and wpg known, show both
        phase = (getattr(p, "phase", "") or "").lower()
        if phase == "liquid" and wpg_val:
            gallons = qty
            pounds = round(qty * wpg_val, 2)

    return gallons, pounds


def compute_inventory_value(p) -> float:
    """
    Inventory value = quantity * unit_cost, assuming unit_cost is per default_unit.
    No hidden conversions for 'unit' items.
    """
    qty_raw = getattr(p, "quantity", 0) or 0
    cost_raw = getattr(p, "unit_cost", 0) or 0
    try:
        qty = float(qty_raw)
    except Exception:
        qty = 0.0
    try:
        cost = float(cost_raw)
    except Exception:
        cost = 0.0
    return round(qty * cost, 2)
