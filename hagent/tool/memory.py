import hashlib

import chromadb
from chromadb.api.types import EmbeddingFunction
from chromadb.utils import embedding_functions

from transformers import AutoTokenizer, AutoModel

import torch
from typing import Dict, List, Optional
from dataclasses import dataclass


def _stable_id(prefix: str, key: str) -> str:
    """Deterministic document ID that is stable across Python invocations."""
    return f'{prefix}_{hashlib.sha256(key.encode()).hexdigest()}'


@dataclass
class Memory_shot:
    question: str
    answer: str
    description: str = ''


class GraphCodeBERTEmbedding(EmbeddingFunction):
    def __init__(self):
        self.tokenizer = AutoTokenizer.from_pretrained('microsoft/graphcodebert-base')
        self.model = AutoModel.from_pretrained('microsoft/graphcodebert-base')
        self.model.eval()

    def __call__(self, input: List[str]) -> List[List[float]]:
        embeddings = []
        with torch.no_grad():
            for text in input:
                tokens = self.tokenizer(text, return_tensors='pt', truncation=True, max_length=512, padding=True)
                outputs = self.model(**tokens)
                embedding = outputs.last_hidden_state[:, 0, :].squeeze().numpy()
                embeddings.append(embedding.tolist())
        return embeddings


# ---------------------------------------------------------------------------
# Base class — ChromaDB plumbing only, no metadata schema opinion
# ---------------------------------------------------------------------------


class BaseMemory:
    """Generic ChromaDB-backed memory with pluggable embeddings.

    Subclasses override ``_embedding_fn()`` and ``_collection_name()``
    then build their own public add/find APIs on top of the low-level
    ``_add`` and ``_query`` primitives.
    """

    def _embedding_fn(self) -> EmbeddingFunction:
        raise NotImplementedError

    def _collection_name(self) -> str:
        raise NotImplementedError

    def __init__(self, learn: bool, db_path: str = './few_shot_memory_db'):
        self.db_path = db_path
        self.learn = learn
        self.client = chromadb.PersistentClient(path=db_path)

        embedding_fn = self._embedding_fn()
        collection_name = self._collection_name()

        try:
            self.collection = self.client.get_collection(
                name=collection_name,
                embedding_function=embedding_fn,
            )
        except Exception:
            self.collection = self.client.create_collection(
                name=collection_name,
                embedding_function=embedding_fn,
            )

    # -- low-level primitives for subclasses --------------------------------

    def _add(self, doc_id: str, document: str, metadata: Dict):
        """Insert or update one document+metadata into the collection.

        Uses upsert so that repeated calls with the same doc_id are
        idempotent instead of creating duplicates.
        """
        if not self.learn:
            return
        return self.collection.upsert(documents=[document], metadatas=[metadata], ids=[doc_id])

    def _query(self, query_text: str, n_results: int = 5, where: Optional[Dict] = None) -> List[Dict]:
        """Return metadata dicts for the *n_results* nearest neighbours."""
        kwargs: Dict = {'query_texts': [query_text], 'n_results': n_results}
        if where:
            kwargs['where'] = where
        results = self.collection.query(**kwargs)
        return results['metadatas'][0]

    def delete(self, doc_ids: List[str]):
        """Delete specific entries by their document IDs."""
        self.collection.delete(ids=doc_ids)

    def clear(self):
        """Drop and re-create the collection, removing all entries."""
        name = self._collection_name()
        embedding_fn = self._embedding_fn()
        self.client.delete_collection(name)
        self.collection = self.client.create_collection(name=name, embedding_function=embedding_fn)


# ---------------------------------------------------------------------------
# Compilation-fix memory  (SentenceTransformer, 384-dim)
# ---------------------------------------------------------------------------


class CompilationFixMemory(BaseMemory):
    """Stores (broken_code -> fixed_code) pairs keyed by error_type.

    Uses SentenceTransformer (all-MiniLM-L6-v2) — lightweight and sufficient
    for matching error messages and short code fragments.
    """

    def _embedding_fn(self) -> EmbeddingFunction:
        return embedding_functions.SentenceTransformerEmbeddingFunction(model_name='all-MiniLM-L6-v2')

    def _collection_name(self) -> str:
        return 'compilation_fix'

    def add(self, error_type: str, fix: Memory_shot):
        doc_id = _stable_id('compilation', error_type + fix.question)
        self._add(
            doc_id=doc_id,
            document=fix.question,
            metadata={
                'fix_question': fix.question,
                'fix_answer': fix.answer,
                'error_type': error_type,
            },
        )

    def find(self, error_type: str, fix_question: str, n_results: int = 5) -> List[Memory_shot]:
        """Semantic search filtered to a specific error_type."""
        metadatas = self._query(
            query_text=fix_question,
            n_results=n_results,
            where={'error_type': {'$eq': error_type}},
        )
        return [Memory_shot(question=m['fix_question'], answer=m['fix_answer']) for m in metadatas]


# Backward-compatible alias — existing code imports FewShotMemory
FewShotMemory = CompilationFixMemory


# ---------------------------------------------------------------------------
# Optimization-technique memory  (GraphCodeBERT, 768-dim)
# ---------------------------------------------------------------------------


class OptimizationMemory(BaseMemory):
    """Stores (before_code -> after_code) optimization technique examples.

    Uses GraphCodeBERT embeddings — trained on source code, better at
    understanding structural code similarity (FSM patterns, mux chains, etc.).
    Lives in a separate collection because the embedding dimensionality
    (768) differs from SentenceTransformer (384).
    """

    def _embedding_fn(self) -> EmbeddingFunction:
        return GraphCodeBERTEmbedding()

    def _collection_name(self) -> str:
        return 'optimization_techniques'

    def add(self, category: str, fix: Memory_shot, description: str = ''):
        doc_id = _stable_id('opt', category + fix.question)
        self._add(
            doc_id=doc_id,
            document=fix.question,
            metadata={
                'before_code': fix.question,
                'after_code': fix.answer,
                'category': category,
                'description': description,
            },
        )

    def find_by_category(self, category: str, query_code: str, n_results: int = 3) -> List[Memory_shot]:
        """Semantic search filtered to a specific optimization category."""
        metadatas = self._query(
            query_text=query_code,
            n_results=n_results,
            where={'category': {'$eq': category}},
        )
        return [
            Memory_shot(question=m['before_code'], answer=m['after_code'], description=m.get('description', ''))
            for m in metadatas
        ]

    def find_similar(self, query_code: str, n_results: int = 3) -> List[Memory_shot]:
        """Semantic search across ALL optimization categories."""
        metadatas = self._query(query_text=query_code, n_results=n_results)
        return [
            Memory_shot(question=m['before_code'], answer=m['after_code'], description=m.get('description', ''))
            for m in metadatas
        ]


# ---------------------------------------------------------------------------
# DesignWare memory  (GraphCodeBERT, 768-dim)
# ---------------------------------------------------------------------------


@dataclass
class DesignWareEntry:
    """A single DesignWare catalog entry returned from a query."""

    pattern: str  # naive RTL code (what to detect)
    replacement: str  # optimized implementation (what to use instead)
    category: str  # e.g. "arithmetic_add", "comparator", "mux"
    description: str  # when/why to use this


class DesignWareMemory(BaseMemory):
    """Stores naive-pattern → optimized-implementation mappings for open DesignWare.

    Uses GraphCodeBERT embeddings (same as OptimizationMemory) for structural
    code similarity matching.  Lives in its own collection ('designware')
    so it does not conflict with optimization-technique entries.

    Typical usage:
        dw = DesignWareMemory(db_path='./memory_db')
        # populate from YAML catalog (see designware_catalog.py)
        dw.add(category='arithmetic_add', pattern='assign sum = a + b;',
               replacement='cla_adder #(.W(W)) ...', description='...')
        # query during optimization
        entries = dw.find_for_code(query_code=original_module_code, n_results=3)
    """

    def _embedding_fn(self) -> EmbeddingFunction:
        return GraphCodeBERTEmbedding()

    def _collection_name(self) -> str:
        return 'designware'

    def add(self, category: str, pattern: str, replacement: str, description: str = ''):
        """Add a DesignWare entry (naive pattern → optimized replacement)."""
        doc_id = _stable_id('dw', category + pattern)
        return self._add(
            doc_id=doc_id,
            document=pattern,
            metadata={
                'pattern': pattern,
                'replacement': replacement,
                'category': category,
                'description': description,
            },
        )

    def find_for_code(self, query_code: str, n_results: int = 3) -> List[DesignWareEntry]:
        """Find DesignWare entries whose patterns are semantically similar to *query_code*."""
        metadatas = self._query(query_text=query_code, n_results=n_results)
        return [
            DesignWareEntry(
                pattern=m['pattern'],
                replacement=m['replacement'],
                category=m.get('category', ''),
                description=m.get('description', ''),
            )
            for m in metadatas
        ]

    def find_by_category(self, category: str, query_code: str, n_results: int = 3) -> List[DesignWareEntry]:
        """Find DesignWare entries filtered to a specific category."""
        metadatas = self._query(
            query_text=query_code,
            n_results=n_results,
            where={'category': {'$eq': category}},
        )
        return [
            DesignWareEntry(
                pattern=m['pattern'],
                replacement=m['replacement'],
                category=m.get('category', ''),
                description=m.get('description', ''),
            )
            for m in metadatas
        ]
