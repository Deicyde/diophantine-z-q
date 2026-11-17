"""Bind a producer's complete input captures across build and full audit.

The trusted driver captures inputs before compilation, after compilation and
after the unchanged full audit. This module checks their equality and stages
outputs only after the real build marker and audit report match. It grants no
GitHub authority: consumers still authenticate the completed run and artifact.
"""
import copy

from kernel_build_manifest import require, validate_inventory
from kernel_build_producer import make_manifest, snapshot_outputs, stage_outputs


def checked_context(context):
    require(isinstance(context, dict) and context.get('schema') == 'kernel-build-context/v1'
            and isinstance(context.get('environment'), dict) and bool(context['environment'])
            and isinstance(context.get('project_paths'), dict), 'Missing complete input context')
    validate_inventory(context.get('modules'))
    require(set(context['project_paths']) == set(context['modules']),
            'Input context does not bind every project module')
    return context


def begin(context):
    """Record the pre-build context, without claiming that a build has run."""
    checked_context(context)
    return {'schema': 'kernel-build-session/v1', 'phase': 'prepared',
            'context': copy.deepcopy(context)}


def record_build(workspace, session, context, build_marker):
    """Refuse a partial build or any input change before recording outputs."""
    require(isinstance(session, dict) and session.get('schema') == 'kernel-build-session/v1'
            and session.get('phase') == 'prepared', 'Expected a prepared build session')
    checked_context(context)
    require(context == session.get('context'), 'Inputs changed during the build')
    require(isinstance(build_marker, dict) and build_marker.get('schema') == 'kernel-build-complete/v1'
            and build_marker.get('status') == 'complete'
            and isinstance(build_marker.get('identity'), dict)
            and build_marker['identity'].get('modules') == sorted(context['modules']),
            'Missing completed build for the exact module inventory')
    outputs = snapshot_outputs(workspace, context['modules'], context['project_paths'])
    return {'schema': 'kernel-build-session/v1', 'phase': 'built',
            'context': copy.deepcopy(context), 'build_marker': copy.deepcopy(build_marker),
            'outputs_before_audit': outputs}


def finish(workspace, destination, session, context, build_marker, audit_report, producer):
    """Stage only stable outputs of an exact, completed full kernel audit.

    No error becomes a cache hit. Partial stages stay diagnostic evidence;
    stage_outputs writes its manifest last. The caller must not upload any
    bundle if this function fails, and must preserve the failure in the job.
    """
    require(isinstance(session, dict) and session.get('schema') == 'kernel-build-session/v1'
            and session.get('phase') == 'built', 'Expected a completed build session')
    checked_context(context)
    require(context == session.get('context'), 'Inputs changed during the full audit')
    require(build_marker == session.get('build_marker'), 'Build marker changed during the full audit')
    after = snapshot_outputs(workspace, context['modules'], context['project_paths'])
    manifest = make_manifest(session['outputs_before_audit'], after,
        session['context']['environment'], context['environment'], build_marker, audit_report, producer)
    staged = stage_outputs(workspace, destination, manifest)
    return {'schema': 'kernel-build-session/v1', 'phase': 'staged',
            'producer': copy.deepcopy(producer), 'staged': staged,
            'audit_report_sha256': manifest['audit_report_sha256'],
            'build_marker_sha256': manifest['build_marker_sha256']}
