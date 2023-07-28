#!/usr/bin/env python3
# Read everest.tar.gz to extract out fst, fsti, checked files
# to be able to run ../QueryCheckedFiles.fst
from typing import *
import tarfile
from tqdm import tqdm
import re
from pysmt.smtlib.parser import SmtLibParser
from dataclasses import dataclass, asdict
import os
import json
from pathlib import Path
import pathlib
import glob
from loguru import logger

def read_info(f : tarfile.TarFile, info : tarfile.TarInfo):
    OUT_DIR_PATH = pathlib.Path("./raw_dataset/")
    os.makedirs(OUT_DIR_PATH, exist_ok=True)
    logger.debug(f"processing '{info.name}'")
    if not info.isfile: return
    path = pathlib.Path(info.name)
    if "fst" in path.suffix or "fsti" in path.suffix or "checked" in path.suffix:
        logger.debug(f"reading '{info.name}'")
        data_handle = f.extractfile(info)
        data = data_handle.read()
        # logger.debug(f"data: '{data}'")
        with open(OUT_DIR_PATH / path.name, "wb") as of:
            of.write(data)
    else:
        logger.debug(f"skippping '{info.name}'")

def read_tar(tarpath : str):
    logger.info(f"opening tarfile '{tarpath}'...")
    f = tarfile.open(tarpath)
    for info in tqdm(f):
        try:
            read_info(f, info)
        except AssertionError as e:
            logger.error(f"  Failed info. Error: '{e}'. continuing...")


read_tar("/home/t-sibhat/guido-everest-dataset/everest_run.tar.gz")
