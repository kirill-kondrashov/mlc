from __future__ import annotations

import sys

from jupyter_client.kernelspec import KernelSpecManager, NoSuchKernel
from jupyter_server.services.contents.largefilemanager import AsyncLargeFileManager
from jupyter_server.services.kernels.kernelmanager import AsyncMappingKernelManager
from jupyterlab.labapp import LabApp
from tornado import web


def _readonly_error(action: str, path: str = "") -> web.HTTPError:
    target = path or "requested content"
    return web.HTTPError(403, f"Read-only JupyterLab: cannot {action} {target}.")


class ReadOnlyContentsManager(AsyncLargeFileManager):
    def is_writable(self, path: str) -> bool:
        return False

    async def save(self, model, path=""):
        raise _readonly_error("save", path)

    async def delete_file(self, path):
        raise _readonly_error("delete", path)

    async def rename_file(self, old_path, new_path):
        raise _readonly_error("rename", f"{old_path} -> {new_path}")

    async def new_untitled(self, path="", type="", ext=""):
        raise _readonly_error("create", path)

    async def new(self, model=None, path=""):
        raise _readonly_error("create", path)

    async def copy(self, from_path, to_path=None):
        target = f"{from_path} -> {to_path}" if to_path else from_path
        raise _readonly_error("copy", target)

    async def update(self, model, path):
        raise _readonly_error("update", path)

    async def create_checkpoint(self, path):
        raise _readonly_error("create checkpoint for", path)

    async def delete_checkpoint(self, checkpoint_id, path):
        raise _readonly_error("delete checkpoint for", path)

    async def restore_checkpoint(self, checkpoint_id, path):
        raise _readonly_error("restore checkpoint for", path)


class NoKernelSpecManager(KernelSpecManager):
    default_kernel_name = ""

    def find_kernel_specs(self):
        return {}

    def get_all_specs(self):
        return {}

    def get_kernel_spec(self, kernel_name):
        raise NoSuchKernel(kernel_name)


class ReadOnlyKernelManager(AsyncMappingKernelManager):
    default_kernel_name = ""

    async def start_kernel(self, *, kernel_id=None, path=None, **kwargs):
        raise _readonly_error("start a kernel for", path or "<root>")

    async def restart_kernel(self, kernel_id, now=False):
        raise _readonly_error("restart kernel", kernel_id)

    def interrupt_kernel(self, kernel_id):
        raise _readonly_error("interrupt kernel", kernel_id)


def main(argv: list[str] | None = None) -> None:
    extra_argv = [
        "--LabApp.extension_manager=readonly",
        "--ServerApp.contents_manager_class=readonly_jupyter.ReadOnlyContentsManager",
        "--ServerApp.kernel_manager_class=readonly_jupyter.ReadOnlyKernelManager",
        "--ServerApp.kernel_spec_manager_class=readonly_jupyter.NoKernelSpecManager",
        "--ServerApp.terminals_enabled=False",
    ]
    LabApp.launch_instance(argv=[*extra_argv, *(argv or sys.argv[1:])])


if __name__ == "__main__":
    main()
