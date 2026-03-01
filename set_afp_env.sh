#!/usr/bin/env bash

# Usage:
#   source ./set_afp_env.sh /path/to/afp
# or:
#   source ./set_afp_env.sh
# In the second form, you will be prompted to input the AFP path
# (supports Tab path completion in bash/zsh interactive shells).

AFP_PATH="${1:-}"

if [ -z "$AFP_PATH" ]; then
  if [ -t 0 ]; then
    if [ -n "${BASH_VERSION:-}" ]; then
      read -e -r -p "Enter AFP root path: " AFP_PATH
    elif [ -n "${ZSH_VERSION:-}" ] && whence -w vared >/dev/null 2>&1; then
      vared -p "Enter AFP root path: " AFP_PATH
    else
      printf "Enter AFP root path: "
      read -r AFP_PATH
    fi
  else
    echo "Error: missing AFP path. Provide /path/to/afp as first argument or run interactively." >&2
    return 1 2>/dev/null || exit 1
  fi
fi

if [ -z "$AFP_PATH" ]; then
  echo "Error: AFP path cannot be empty." >&2
  return 1 2>/dev/null || exit 1
fi

AFP_PATH="${AFP_PATH/#\~/$HOME}"

if [ ! -d "$AFP_PATH" ]; then
  echo "Error: AFP path does not exist: $AFP_PATH" >&2
  return 1 2>/dev/null || exit 1
fi

if [ ! -d "$AFP_PATH/thys" ]; then
  echo "Error: AFP path must contain a thys/ directory: $AFP_PATH" >&2
  return 1 2>/dev/null || exit 1
fi

export AFP="$AFP_PATH"
echo "AFP is set to: $AFP"
echo "AFP thys directory: $AFP/thys"
