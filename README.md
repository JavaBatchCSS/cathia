# CathIA

Application web de conception 3D pour le froissartage (construction scoute en bois) : traverses, tenons, mi-bois, filets, mise en plan cotée avec nomenclatures, bibliothèques de modèles, montage pas à pas.

## Deux façons de l'utiliser

| | Adresse | Particularités |
|---|---|---|
| **Version GitHub Pages** (recommandée) | `https://javabatchcss.github.io/cathia/` | chargement rapide, aucune dépendance au compte Google du navigateur |
| Version Google Apps Script | adresse `/exec` du déploiement | conservée en parallèle |

Les deux versions utilisent le même fichier `index.html` et le même serveur Apps Script (`Code.gs`) pour les bibliothèques et la publication. Les projets de chaque utilisateur sont enregistrés **dans son propre Google Drive** (accès limité aux fichiers créés par CathIA).

## Organisation

- `src/` : sources (`shell.html`, `app.js`, `extra.js`, `cloud.js`, `thumbs.js`)
- `build.js` : assemble `index.html` (`node build.js`)
- `Code.gs`, `appsscript.json` : serveur Apps Script (déployé avec `clasp`)
- `index.html` : fichier généré, servi par GitHub Pages

## Mise à jour

```
node build.js          # régénère index.html
git add -A && git commit && git push   # GitHub Pages se met à jour tout seul
clasp push --force     # serveur Apps Script (si Code.gs a changé)
```

Propriétés du script Apps Script à renseigner : `GOOGLE_CLIENT_ID`, `GOOGLE_CLIENT_SECRET`, `APP_URL`.
