"""
MIT License
Copyright (c) 2015 Aaron Hall
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:
The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.
THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
"""

from __future__ import annotations

import threading
from typing import Any, Callable, TypeVar

_F = TypeVar("_F", bound=Callable[..., Any])

# Use _thread module (Python 3 name for the legacy thread module)
import _thread


def cdquit(fn_name: str) -> None:
    """Interrupt the main thread."""
    _thread.interrupt_main()  # raises KeyboardInterrupt


def exit_after(s: int) -> Callable[[Callable[..., Any]], Callable[..., Any]]:
    """
    Decorator to exit the process if the function takes longer than s seconds.

    Parameters
    ----------
    s : int
        Maximum allowed execution time in seconds.

    Returns
    -------
    Callable
        A decorator that wraps functions with a timeout.
    """

    def outer(fn: Callable[..., Any]) -> Callable[..., Any]:
        def inner(*args: Any, **kwargs: Any) -> Any:
            timer = threading.Timer(s, cdquit, args=[fn.__name__])
            timer.start()
            try:
                result = fn(*args, **kwargs)
            finally:
                timer.cancel()
            return result

        return inner

    return outer
