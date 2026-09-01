#!/bin/bash
cd /home/sharjeelhasan33/ShajjiGoldSignals
set -a
source .env
set +a

HC_URL="https://hc-ping.com/535fde16-7c83-4ab7-bbc2-b84f6c11745c"

while true; do
    echo "$(date): Starting scan"
    python3 xau_bot.py
    EXIT_CODE=$?
    if [ $EXIT_CODE -eq 0 ]; then
        curl -fsS -m 10 --retry 3 "$HC_URL" > /dev/null
        echo "$(date): Scan finished OK, pinged healthcheck"
    else
        curl -fsS -m 10 --retry 3 "$HC_URL/fail" > /dev/null
        echo "$(date): Scan FAILED (exit $EXIT_CODE), pinged healthcheck fail"
    fi

    NOW_MIN=$(date +%-M)
    NOW_SEC_ONLY=$(date +%-S)
    MIN_INTO_5=$(( NOW_MIN % 5 ))
    SECS_SINCE_CANDLE=$(( MIN_INTO_5 * 60 + NOW_SEC_ONLY ))
    SLEEP_TIME=$(( 300 - SECS_SINCE_CANDLE + 20 ))
    if [ $SLEEP_TIME -lt 10 ]; then
        SLEEP_TIME=$(( SLEEP_TIME + 300 ))
    fi
    sleep $SLEEP_TIME
done
