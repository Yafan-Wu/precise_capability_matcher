# Präziser Capability Matcher – README (Deutsch)

## 1  Überblick  
Der **Precise Capability Matcher** ist ein plattformunabhängiges Python-Tool mit grafischer Benutzeroberfläche (tkinter). Es verknüpft **Rezept-Schritte** (Recipe JSON) mit **AAS-Fähigkeiten** (Capabilities JSON) eines oder mehrerer Ressourcen und zeigt alle passenden Capability-Einträge übersichtlich an.  
Hauptziel: **vollständige, nachvollziehbare und mehrfache Zuordnung** (one-to-many) einschließlich detaillierter Debug-Infos und CSV-Export.

---

## 2  Kernfunktionen  

| Funktionsbereich | Beschreibung |
|------------------|--------------|
| **Intelligentes Matching** | • Synonym-Wörterbuch & Normalisierung (z. B. *rpm* → *RevolutionsPerMinute*)<br>• Operatoren ≥ ≤ < > =<br>• Bereichs- und Vergleichslogik |
| **Mehrfach-Treffer** | Ein Rezept-Schritt kann mehrere Fähigkeiten erfüllen (z. B. *StirringContinuous*, *StirringDuration*, …). Jede Übereinstimmung wird als eigene Zeile ausgegeben. |
| **GUI-Workflow** | Buttons zum Laden von Dateien, Starten des Abgleichs, CSV-Export und Anzeigen eines Debug-Reports. |
| **Vollständiger Debug-Report** | Klick auf „Debug Report“ öffnet ein Fenster mit einer ausführlichen Schritt-für-Schritt-Protokollierung aller Prüfungen. |
| **CSV-Export** | Ergebnisse lassen sich für weitere Auswertungen als CSV speichern. |
| **Logging** | `logging`-Modul mit umschaltbarem Detailgrad (`DEBUG = True/False`). |

---

## 3  Voraussetzungen  

| Komponente | Version / Hinweis |
|------------|------------------|
| **Python** | ≥ 3.8 (getestet bis 3.12) |
| **Tkinter** | Wird in den meisten Python-Distributionen standardmäßig mitgeliefert. |
| **Zusatz-Bibliotheken** | *Keine externen Pakete erforderlich* (nur Standardbibliothek). |

---

## 4  Installation  

```bash
# 1. Repository klonen oder Datei herunterladen
git clone <repo-url> capability-matcher
cd capability-matcher

# 2. (Optional) Virtuelle Umgebung anlegen
python -m venv .venv
source .venv/bin/activate          # Linux/macOS
.venv\Scripts\activate             # Windows

# 3. Script starten
python precise_capability_matcher.py
