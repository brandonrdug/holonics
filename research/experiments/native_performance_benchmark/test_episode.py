from contextlib import closing
import json
from pathlib import Path
import sqlite3
import tempfile
import unittest

import episode


class EpisodeBoundaryTest(unittest.TestCase):
    def package(self, directory):
        path=directory/'source.sqlite'
        with closing(sqlite3.connect(path)) as db, db:
            db.executescript(episode.corpus.DDL)
            db.execute("INSERT INTO sources(id,provider,path,captured_octets,mtime_ns) VALUES(1,'codex','private-log',100,0)")
            for i,role,text,time in [(1,'human','earlier source','00:00:00'),(2,'human','actual request','00:01:00'),(3,'agent','candidate answer','00:02:00'),(4,'human','later correction','00:03:00')]:
                db.execute("INSERT INTO events(id,source,record_number,byte_start,byte_end,timestamp,author_class,record_kind,flags,provider_metadata,raw_zlib) VALUES(?,1,?,0,1,?,?,'message','[]','{}',X'00')",(i,i,'2026-09-01T'+time+'Z',role))
                db.execute("INSERT INTO parts(event,ordinal,pointer,kind,text) VALUES(?,0,'/text',?,?)",(i,'human-text' if role=='human' else 'agent-text',text))
            db.execute("INSERT INTO comparisons VALUES(2,3,'declared test relation')")
            db.execute("INSERT INTO links VALUES(4,3,'later-human-after-agent',NULL,'test relation')")
        return path

    def test_candidate_and_later_feedback_stay_outside_input(self):
        with tempfile.TemporaryDirectory() as directory:
            d=Path(directory);path=self.package(d);out=d/'episode'
            receipt=episode.prepare(path,2,[1],[],out)
            source=(out/'input.json').read_text();assessment=(out/'assessment.json').read_text()
            self.assertNotIn('candidate answer',source)
            self.assertNotIn('later correction',source)
            self.assertIn('candidate answer',assessment)
            self.assertIn('later correction',assessment)
            self.assertFalse(json.loads(assessment)['assistant_is_gold'])
            self.assertEqual(receipt['recorded_candidates'],1)
            self.assertEqual((out/'input.json').stat().st_mode&0o777,0o600)
            with self.assertRaises(FileExistsError):episode.prepare(path,2,[1],[],out)

    def test_response_or_future_context_is_rejected(self):
        with tempfile.TemporaryDirectory() as directory:
            d=Path(directory);path=self.package(d)
            for ids in ([3],[4],[2]):
                with self.assertRaises(ValueError):episode.prepare(path,2,ids,[],d/'rejected')
            self.assertFalse((d/'rejected').exists())


if __name__=='__main__':unittest.main()
