# BTC Scalp Bot v6 — Server Edition

Серверный порт браузерного скальп-бота. Работает 24/7 на Railway.

## Архитектура

```
server.js         ← всё ядро: Coinbase WS, Polymarket API, Chainlink, 4 стратегии
public/index.html ← веб-дашборд (Server-Sent Events, обновляется каждую секунду)
state.json        ← персистентное состояние (баланс, открытые позиции, лог)
```

## Деплой на Railway

### 1. Создай репозиторий на GitHub

```bash
git init
git add .
git commit -m "btc-scalp-bot v6"
git branch -M main
git remote add origin https://github.com/ТВОЙ_ЮЗЕР/btc-scalp-bot.git
git push -u origin main
```

### 2. Создай проект на Railway

1. Открой [railway.app](https://railway.app)
2. **New Project → Deploy from GitHub repo**
3. Выбери репозиторий `btc-scalp-bot`
4. Railway автоматически определит Node.js и запустит `node server.js`

### 3. Добавь Volume (для сохранения state.json между рестартами)

1. В проекте Railway → **+ Add** → **Volume**
2. Mount Path: `/app/data`
3. Затем в `server.js` измени строку:
   ```js
   const STATE_FILE = path.join('/app/data', 'state.json');
   ```
   и сделай коммит.

### 4. Открой дашборд

Railway даст публичный URL вида `https://btc-scalp-bot-production.up.railway.app`

## API

| Endpoint | Описание |
|---|---|
| `GET /` | Веб-дашборд |
| `GET /events` | SSE-поток обновлений (раз в секунду) |
| `GET /api/state` | Текущее состояние JSON |
| `POST /api/strategy/:id/toggle` | Включить/выключить стратегию |
| `POST /api/strategy/:id/reset` | Сбросить стратегию (баланс $1000, лог пуст) |
| `GET /api/export/csv` | Скачать лог всех сделок |

ID стратегий: `momentum`, `meanRev`, `bookImb`, `vwapRev`

## Стратегии (сейчас в демо-режиме)

| Стратегия | Логика |
|---|---|
| **Momentum** | Высокая уверенность модели (>35%) + edge ≥ 3pp против Polymarket |
| **Mean Reversion** | Против шары > 78¢ в последние 30-120с окна |
| **Book Imbalance** | Имбаланс Polymarket CLOB стакана > 40% |
| **VWAP Reversion** | BTC > 1.5 ATR от VWAP за 60с → ставит на возврат |

## Режим Simulation

Если Coinbase WebSocket недоступен (блокировка), бот автоматически переходит в режим симуляции (`● sim mode` в дашборде). Все стратегии продолжают работать на симулированных данных.

## Для реальной торговли (следующий шаг)

Нужно будет добавить:
1. `POLY_PRIVATE_KEY` — приватный ключ Polygon-кошелька
2. Функцию `placeClobOrder()` через Polymarket CLOB API (подпись EIP-712)
3. Флаг `REAL_TRADING=true` в env Railway

До этого бот торгует **только в демо** — отслеживает сделки в памяти, не тратит реальных средств.

---

## Обновления (управление с дашборда)

В дашборд добавлен блок **⚙️ Настройки** (под карточками стратегий):

### Режим направления — Инверсия
Кнопка **ИНВЕРСИЯ ON/OFF**. По умолчанию OFF (торгуем ПО сигналу модели).
Включённая инверсия заставляет бота заходить в ПРОТИВОПОЛОЖНУЮ сторону
(UP↔DOWN) — для A/B-проверки гипотезы «сигнал перевёрнут». Применяется на лету,
сохраняется между рестартами. В логах сделок при инверсии метка `[INV]`.

### Кастомные параметры входа
Кнопка **КАСТОМ ON/OFF** + поля: Edge, Уверенность, Take Profit, Stop Loss,
Разворот, Adverse move, Kelly, Макс. доля баланса, Мин. время до конца.
- OFF → работают базовые значения (`def.defaults`).
- ON → применяются значения из полей (после «💾 Сохранить параметры»).
- «↺ Сброс к базе» — вернуть дефолты.
- Под полями показывается точка безубытка = SL/(TP+SL).

### Новые API-эндпоинты
| Endpoint | Описание |
|---|---|
| `POST /api/invert/toggle` | Переключить инверсию (`{enabled?}` или флип) |
| `POST /api/strategy/:id/custom/toggle` | Вкл/выкл кастом-режим |
| `POST /api/strategy/:id/params` | Задать кастомные параметры (числа) |
| `POST /api/strategy/:id/params/reset` | Сбросить к базе |

Все настройки персистятся в `state.json` и переживают рестарт.

## Переменные окружения (опционально)
| Переменная | Значение по умолчанию | Описание |
|---|---|---|
| `INVERT_SIGNAL` | `false` | Стартовое состояние инверсии (потом крутится с дашборда) |
| `TP_ABS_PRICE` | `0.95` | Абсолютный потолок тейк-профита (¢) |
| `BUY_SLIPPAGE` | `0.05` | Проскальзывание вверх при входе по рынку |
| `PANIC_SELL` | `true` | Рыночный сброс позиции при неудачном лимитном выходе |
| `REAL_TRADING` | `false` | Включение реальной торговли |

---

## Стратегии (v8)

Каждая стратегия торгует независимо, со своими demo/real аккаунтами, логом и
карточкой на дашборде. Новые (кроме momentum) по умолчанию ВЫКЛЮЧЕНЫ — включаются
тумблером. Тестировать на demo, real не трогать до устойчивого плюса на выборке.

| ID | Название | Логика входа | Выход |
|---|---|---|---|
| `momentum` | Momentum / Trend | сигнал модели + edge ≥ порог | TP / SL / FLIP / ADVERSE |
| `momScratch` | Momentum Scratch | как momentum | + SCRATCH: фиксация малой прибыли, если TP недостижим и импульс выдохся / мало времени |
| `antiMom` | Anti-Momentum | всегда ПРОТИВ сигнала модели (зеркало momentum) | TP / SL / ADVERSE |
| `meanRev` | Mean Reversion | против перегретой стороны (>80¢) в середине окна | TP / SL |
| `lateFav` | Late Favorite | в конце окна — фаворит по факту BTC, пока < 93¢ | TP / SL / фаворит потерян |
| `bookImb` | Order-Book Imbalance | направление по дисбалансу стакана BTC > порога | TP / SL / ADVERSE |

Глобальный тумблер ИНВЕРСИЯ влияет на `momentum` и `momScratch`. `antiMom` —
всегда зеркало сырого сигнала (для чистого A/B momentum vs anti держи ИНВЕРСИЮ OFF).
