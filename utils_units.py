# utils_units.py
def normalize_unit(u: str) -> str:
    u = (u or "").strip().lower()
    if u in {"gallon", "gallons", "gal"}:
        return "gal"
    if u in {"pound", "pounds", "lb", "lbs"}:
        return "lb"
    if u in {"unit", "units", "ea", "each", "tote", "totes", "drum", "drums", "cooler", "coolers", "ibc", "ibcs"}:
        return "unit"
    # Be conservative: default to 'unit' rather than forcing weight
    return u or "unit"
