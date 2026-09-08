# TradeGuard Live V3

Moteur d'analyse crypto temps réel + alertes Telegram.

## Important
- Ce projet est un scanner/paper-trading, pas un système de garantie de gains.
- Les horizons de quelques secondes sont extrêmement bruités et sensibles aux frais, spread et slippage.
- Le score n'est PAS une probabilité de gain.
- Le moteur refuse les signaux faibles et applique des limites d'alerte.

## Lancer
1. Installer Node.js 20+.
2. Copier `.env.example` vers `.env`.
3. Mettre le token du bot Telegram dans `TELEGRAM_BOT_TOKEN`.
4. `npm install`
5. `npm start`

Pour scanner d'autres symboles Binance, mettre `SYMBOLS=btcusdt,ethusdt,...`.

## Adaptateurs Trench / autres plateformes
Le moteur est séparé du canal Telegram. Pour une plateforme qui fournit un flux WebSocket/API, ajouter un adaptateur qui appelle `ingest(symbol,{t,p,q})`. Ne jamais envoyer d'ordre réel sans avoir validé le moteur sur une longue période en paper trading.
